version     = "0.0.1"
author      = "Balazs Komuves"
description = "Groth16 proof system"
license     = "MIT OR Apache-2.0"

skipDirs    = @["groth16/example"]
binDir      = "build"
namedBin    = {"cli/cli_main": "nim-groth16"}.toTable()

requires "https://github.com/status-im/nim-taskpools"
requires "https://github.com/mratsim/constantine#5f7ba18f2ed351260015397c9eae079a6decaee1"