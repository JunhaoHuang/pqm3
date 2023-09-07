#!/usr/bin/env python3

import datetime
import subprocess
import sys
import re
import serial
import numpy as np
from config import Settings
import os.path

def toLog(name, value, k=None):
  if value > 20000:
    value = f"{round(value/1000)}k"
  else:
    value = f"{value}"
  return f"{name}: {value}\n"

def toMacro(name, value, k=None):
  if value > 20000:
    value = f"{round(value/1000):,}k"
  else:
    value = f"{value:,}"
  value = value.replace(",", "\\,")
  return f"\\DefineVar{{{name}}}{{{value}}}\n"

def run_bench(scheme_path, scheme_name, scheme_type, iterations):
    # subprocess.check_call(f"make clean", shell=True)
    subprocess.check_call(f"make PLATFORM=sam3x8e IMPLEMENTATION_PATH={scheme_path} MUPQ_ITERATIONS={iterations} ./bin/{scheme_name}_speed.bin", shell=True)
    binary = f"./bin/{scheme_name}_speed.bin"
    if os.path.isfile(binary) is False:
        print("Binary does not exist")
        exit()

    try:
        subprocess.check_call(f"bossac -a --erase --write --verify --boot=1 --port=/dev/ttyACM0 ./bin/{scheme_name}_speed.bin", shell=True)
    except:
        print("bossac write failed --> retry")
        return run_bench(scheme_path, scheme_name, scheme_type, iterations)

    # get serial output and wait for '#'
    with serial.Serial(Settings.SERIAL_DEVICE, 9600, timeout=10) as dev:
        logs = []
        iteration = 0
        log = b""
        while iteration < iterations:
            device_output = dev.read()
            if device_output == b'':
                print("timeout --> retry")
                return run_bench(scheme_path, scheme_name, scheme_type, iterations)
            sys.stdout.buffer.write(device_output)
            sys.stdout.flush()
            log += device_output
            if device_output == b'#':
                logs.append(log)
                log = b""
                iteration += 1
    return logs


def parseLogSpeed(log, ignoreErrors):
    log = log.decode(errors="ignore")
    if "error" in log.lower() and not ignoreErrors:
        raise Exception("error in scheme. this is very bad.")
    lines = str(log).splitlines()
    def get(lines, key):
        if key in lines:
            return int(lines[1+lines.index(key)])
        else:
            return None

    def cleanNullTerms(d):
        return {
            k:v
            for k, v in d.items()
            if v is not None
        }

    return cleanNullTerms({
        f"ntt":  get(lines, "ntt cycles:"),
        f"invntt":  get(lines, "invntt cycles:"),
        f"basemul":  get(lines, "basemul cycles:"),
        f"poly_basemul_opt_16_32":  get(lines, "poly_basemul_opt_16_32 cycles:"),
        f"poly_basemul_acc_opt_32_32":  get(lines, "poly_basemul_acc_opt_32_32 cycles:"),
        f"poly_basemul_acc_opt_32_16":  get(lines, "poly_basemul_acc_opt_32_16 cycles:"),
        f"ntt_leaktime":  get(lines, "ntt leaktime cycles:"),
        f"invntt_leaktime":  get(lines, "invntt leaktime cycles:"),
        f"basemul_leaktime":  get(lines, "basemul leaktime cycles:"),
        f"cs1_32ntt":  get(lines, "cs1 with 32-bit NTT cycles:"),
        f"cs2_32ntt":  get(lines, "cs2 with 32-bit NTT cycles:"),
        f"ct0_con_var_32ntt":  get(lines, "ct0 part-constant part-variable with 32-bit NTT cycles:"),
        f"ct1_var_32ntt":  get(lines, "ct1 variable time with 32-bit NTT cycles:"),
        f"multi_moduli_ntt":  get(lines, "multi-moduli ntt cycles:"),
        f"multi_moduli_ntt_precomp":  get(lines, "multi-moduli ntt precomp cycles:"),
        f"poly_double_basemul_invntt":  get(lines, "multi-moduli basemul+intt cycles:"),
        f"double_CRT":  get(lines, "multi-moduli double crt cycles:"),
        f"cs1_16ntt":  get(lines, "cs1 small NTT cycles:"),
        f"cs2_16ntt":  get(lines, "cs2 small NTT cycles:"),
        f"ct0_multi_moduli_ntt":  get(lines, "ct0 double NTT cycles:"),
    })

def average(results):
    avgs = dict()
    for key in results[0].keys():
        avgs[key] = int(np.array([results[i][key] for i in range(len(results))]).mean())
    return avgs


def bench(scheme_path, scheme_name, scheme_type, iterations, outfile, ignoreErrors=False):
    logs    = run_bench(scheme_path, scheme_name, scheme_type, iterations)
    results = []
    for log in logs:
        try:
            result = parseLogSpeed(log, ignoreErrors)
        except:
            breakpoint()
            print("parsing log failed -> retry")
            return bench(scheme_path, scheme_name, scheme_type, iterations, outfile)
        results.append(result)
    avgResults = average(results)
    print(f"%M3 results for {scheme_name} (type={scheme_type})", file=outfile)
    scheme_nameStripped = scheme_name.replace("-", "") 
    for key, value in avgResults.items():
        macro = toMacro(f"{scheme_nameStripped}{key}", value)
        print(macro.strip())
        print(macro, end='', file=outfile)
    print('', file=outfile, flush=True)


with open(f"poly_benchmarks.txt", "a") as outfile:

    now = datetime.datetime.now(datetime.timezone.utc)
    iterations = 1 # defines the number of measurements to perform
    print(f"% Polynomial arithmetic benchmarking measurements written on {now}; iterations={iterations}\n", file=outfile)

    # subprocess.check_call(f"make clean", shell=True)

    # uncomment the scheme variants that should be build and evaluated
    for scheme_path in [
        # "crypto_kem/kyber512/m3",
        # "crypto_kem/kyber512/m3fspeed",
        # "crypto_kem/kyber512/m3fstack",
        # "crypto_kem/kyber768/m3",
        # "crypto_kem/kyber768/m3fspeed",
        # "crypto_kem/kyber768/m3fstack",
        # "crypto_kem/kyber1024/m3",
        # "crypto_kem/kyber1024/m3fspeed",
        # "crypto_kem/kyber1024/m3fstack",
        "crypto_sign/dilithium2/m3",
        "crypto_sign/dilithium2/m3plant"
    ]:
        scheme_name = scheme_path.replace("/", "_")
        scheme_type = re.search('crypto_(.*?)_', scheme_name).group(1)
        bench(scheme_path, scheme_name, scheme_type, iterations, outfile)




