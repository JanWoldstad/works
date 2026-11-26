import WildNumber.Orbit.L0x0
import WildNumber.Orbit.L1x0
import WildNumber.Orbit.L2x0
import WildNumber.Orbit.L3x0
import WildNumber.Orbit.L4x0
import WildNumber.Orbit.L5x0
import WildNumber.Orbit.L6x0
import WildNumber.Orbit.L6x32
import WildNumber.Orbit.L7x0
import WildNumber.Orbit.L7x32
import WildNumber.Orbit.L7x64
import WildNumber.Orbit.L7x96
import WildNumber.Orbit.L8x0
import WildNumber.Orbit.L8x32
import WildNumber.Orbit.L8x64
import WildNumber.Orbit.L8x96
import WildNumber.Orbit.L8x128
import WildNumber.Orbit.L8x160
import WildNumber.Orbit.L8x192
import WildNumber.Orbit.L9x0
import WildNumber.Orbit.L9x32
import WildNumber.Orbit.L9x64
import WildNumber.Orbit.L9x96
import WildNumber.Orbit.L9x128
import WildNumber.Orbit.L9x160
import WildNumber.Orbit.L9x192
import WildNumber.Orbit.L9x224
import WildNumber.Orbit.L9x256
import WildNumber.Orbit.L9x288
import WildNumber.Orbit.L9x320
import WildNumber.Orbit.L9x352
import WildNumber.Orbit.L9x384
import WildNumber.Orbit.L10x0
import WildNumber.Orbit.L10x32
import WildNumber.Orbit.L10x64
import WildNumber.Orbit.L10x96
import WildNumber.Orbit.L10x128
import WildNumber.Orbit.L10x160
import WildNumber.Orbit.L10x192
import WildNumber.Orbit.L10x224
import WildNumber.Orbit.L10x256
import WildNumber.Orbit.L10x288
import WildNumber.Orbit.L10x320
import WildNumber.Orbit.L10x352
import WildNumber.Orbit.L10x384
import WildNumber.Orbit.L10x416
import WildNumber.Orbit.L10x448
import WildNumber.Orbit.L10x480
import WildNumber.Orbit.L10x512
import WildNumber.Orbit.L10x544
import WildNumber.Orbit.L10x576
import WildNumber.Orbit.L10x608
import WildNumber.Orbit.L10x640

namespace WildNumber.Nine.Orbit

theorem checked0 : CoversRows level0 level1 0 1 := by
  exact chunkL0x0

theorem checked1 : CoversRows level1 level2 0 1 := by
  exact chunkL1x0

theorem checked2 : CoversRows level2 level3 0 2 := by
  exact chunkL2x0

theorem checked3 : CoversRows level3 level4 0 5 := by
  exact chunkL3x0

theorem checked4 : CoversRows level4 level5 0 11 := by
  exact chunkL4x0

theorem checked5 : CoversRows level5 level6 0 24 := by
  exact chunkL5x0

theorem checked6 : CoversRows level6 level7 0 56 := by
  apply rows_append (m := 32) (n := 24) chunkL6x0
  exact chunkL6x32

theorem checked7 : CoversRows level7 level8 0 115 := by
  apply rows_append (m := 32) (n := 83) chunkL7x0
  apply rows_append (m := 32) (n := 51) chunkL7x32
  apply rows_append (m := 32) (n := 19) chunkL7x64
  exact chunkL7x96

theorem checked8 : CoversRows level8 level9 0 221 := by
  apply rows_append (m := 32) (n := 189) chunkL8x0
  apply rows_append (m := 32) (n := 157) chunkL8x32
  apply rows_append (m := 32) (n := 125) chunkL8x64
  apply rows_append (m := 32) (n := 93) chunkL8x96
  apply rows_append (m := 32) (n := 61) chunkL8x128
  apply rows_append (m := 32) (n := 29) chunkL8x160
  exact chunkL8x192

theorem checked9 : CoversRows level9 level10 0 402 := by
  apply rows_append (m := 32) (n := 370) chunkL9x0
  apply rows_append (m := 32) (n := 338) chunkL9x32
  apply rows_append (m := 32) (n := 306) chunkL9x64
  apply rows_append (m := 32) (n := 274) chunkL9x96
  apply rows_append (m := 32) (n := 242) chunkL9x128
  apply rows_append (m := 32) (n := 210) chunkL9x160
  apply rows_append (m := 32) (n := 178) chunkL9x192
  apply rows_append (m := 32) (n := 146) chunkL9x224
  apply rows_append (m := 32) (n := 114) chunkL9x256
  apply rows_append (m := 32) (n := 82) chunkL9x288
  apply rows_append (m := 32) (n := 50) chunkL9x320
  apply rows_append (m := 32) (n := 18) chunkL9x352
  exact chunkL9x384

theorem checked10 : CoversRows level10 level11 0 663 := by
  apply rows_append (m := 32) (n := 631) chunkL10x0
  apply rows_append (m := 32) (n := 599) chunkL10x32
  apply rows_append (m := 32) (n := 567) chunkL10x64
  apply rows_append (m := 32) (n := 535) chunkL10x96
  apply rows_append (m := 32) (n := 503) chunkL10x128
  apply rows_append (m := 32) (n := 471) chunkL10x160
  apply rows_append (m := 32) (n := 439) chunkL10x192
  apply rows_append (m := 32) (n := 407) chunkL10x224
  apply rows_append (m := 32) (n := 375) chunkL10x256
  apply rows_append (m := 32) (n := 343) chunkL10x288
  apply rows_append (m := 32) (n := 311) chunkL10x320
  apply rows_append (m := 32) (n := 279) chunkL10x352
  apply rows_append (m := 32) (n := 247) chunkL10x384
  apply rows_append (m := 32) (n := 215) chunkL10x416
  apply rows_append (m := 32) (n := 183) chunkL10x448
  apply rows_append (m := 32) (n := 151) chunkL10x480
  apply rows_append (m := 32) (n := 119) chunkL10x512
  apply rows_append (m := 32) (n := 87) chunkL10x544
  apply rows_append (m := 32) (n := 55) chunkL10x576
  apply rows_append (m := 32) (n := 23) chunkL10x608
  exact chunkL10x640

end WildNumber.Nine.Orbit
