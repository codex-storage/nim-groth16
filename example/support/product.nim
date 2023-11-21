
{.passc: gorge("pkg-config --cflags gmp nlohmann_json").}
{.passl: gorge("pkg-config --libs gmp nlohmann_json").}

when defined(arm64):
  {.passc: "-D_LONG_LONG_LIMB".}
  {.compile("fr_raw_arm64.s", "-O3 -DNDEBUG -arch arm64 -fPIC -D_LONG_LONG_LIMB").}
  {.compile: "fr_raw_generic.cpp".}
  {.compile: "fr_generic.cpp".}
else:
  {.compile: "fr.asm".}

{.compile: "fr.cpp".}
{.compile: "calcwit.cpp".}
{.compile: "witnesscalc.cpp".}
{.compile: "circuits_incl.cpp".}
# {.compile: "product.cpp".}
{.compile: "main.cpp".}
