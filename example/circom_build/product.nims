
--backend:cpp
--noMain:on
--nimcache:nimcache
--verbosity:2

{.passc: gorge("pkg-config --cflags gmp nlohmann_json").}
{.passl: gorge("pkg-config --libs gmp nlohmann_json").}

when defined(arm64):
  static:
    echo "INCLUDE ARM"
  {.passc: "-D_LONG_LONG_LIMB -DUSE_ASM".}
  {.compile("fr_raw_arm64.s", "-O3 -DNDEBUG -DARCH_ARM64 -arch arm64 -fPIC -D_LONG_LONG_LIMB").}
  {.compile: "fr_raw_generic.cpp".}
  {.compile: "fr_generic.cpp".}
else:
  {.compile: "fr.asm".}

{.compile: "fr.cpp".}
{.compile: "calcwit.cpp".}
{.compile: "witnesscalc.cpp".}

# {.compile: "../build/product_cpp/product.cpp".}
# {.compile: "../build/product_cpp/main.cpp".}
{.compile: "main.cpp".}
