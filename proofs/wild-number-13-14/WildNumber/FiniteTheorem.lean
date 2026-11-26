import WildNumber.FiniteCertificates.Batch000
import WildNumber.FiniteCertificates.Batch001
import WildNumber.FiniteCertificates.Batch002
import WildNumber.FiniteCertificates.Batch003
import WildNumber.FiniteCertificates.Batch004
import WildNumber.FiniteCertificates.Batch005
import WildNumber.FiniteCertificates.Batch006
import WildNumber.FiniteCertificates.Batch007
import WildNumber.FiniteCertificates.Batch008
import WildNumber.FiniteCertificates.Batch009
import WildNumber.FiniteCertificates.Batch010
import WildNumber.FiniteCertificates.Batch011
import WildNumber.FiniteCertificates.Batch012
import WildNumber.FiniteCertificates.Batch013
import WildNumber.FiniteCertificates.Batch014
import WildNumber.FiniteCertificates.Batch015
import WildNumber.FiniteCertificates.Batch016
import WildNumber.FiniteCertificates.Batch017
import WildNumber.FiniteCertificates.Batch018
import WildNumber.FiniteCertificates.Batch019
import WildNumber.FiniteCertificates.Batch020
import WildNumber.FiniteCertificates.Batch021
import WildNumber.FiniteCertificates.Batch022
import WildNumber.FiniteCertificates.Batch023
import WildNumber.FiniteCertificates.Batch024
import WildNumber.FiniteCertificates.Batch025
import WildNumber.FiniteCertificates.Batch026
import WildNumber.FiniteCertificates.Batch027
import WildNumber.FiniteCertificates.Batch028
import WildNumber.FiniteCertificates.Batch029
import WildNumber.FiniteCertificates.Batch030
import WildNumber.FiniteCertificates.Batch031
import WildNumber.FiniteCertificates.Batch032
import WildNumber.FiniteCertificates.Batch033
import WildNumber.FiniteCertificates.Batch034
import WildNumber.FiniteCertificates.Batch035
import WildNumber.FiniteCertificates.Batch036
import WildNumber.FiniteCertificates.Batch037
import WildNumber.FiniteCertificates.Batch038
import WildNumber.FiniteCertificates.Batch039
import WildNumber.FiniteCertificates.Batch040
import WildNumber.FiniteCertificates.Batch041
import WildNumber.FiniteCertificates.Batch042
import WildNumber.FiniteCertificates.Batch043
import WildNumber.FiniteCertificates.Batch044
import WildNumber.FiniteCertificates.Batch045
import WildNumber.FiniteCertificates.Batch046
import WildNumber.FiniteCertificates.Batch047
import WildNumber.FiniteCertificates.Batch048
import WildNumber.FiniteCertificates.Batch049
import WildNumber.FiniteCertificates.Batch050
import WildNumber.FiniteCertificates.Batch051
import WildNumber.FiniteCertificates.Batch052
import WildNumber.FiniteCertificates.Batch053
import WildNumber.FiniteCertificates.Batch054
import WildNumber.FiniteCertificates.Batch055
import WildNumber.FiniteCertificates.Batch056
import WildNumber.FiniteCertificates.Batch057
import WildNumber.FiniteCertificates.Batch058
import WildNumber.FiniteCertificates.Batch059
import WildNumber.FiniteCertificates.Batch060
import WildNumber.FiniteCertificates.Batch061
import WildNumber.FiniteCertificates.Batch062
import WildNumber.FiniteCertificates.Batch063
import WildNumber.FiniteCertificates.Batch064
import WildNumber.FiniteCertificates.Batch065
import WildNumber.FiniteCertificates.Batch066
import WildNumber.FiniteCertificates.Batch067
import WildNumber.FiniteCertificates.Batch068
import WildNumber.FiniteCertificates.Batch069
import WildNumber.FiniteCertificates.Batch070
import WildNumber.FiniteCertificates.Batch071
import WildNumber.FiniteCertificates.Batch072
import WildNumber.FiniteCertificates.Batch073
import WildNumber.FiniteCertificates.Batch074
import WildNumber.FiniteCertificates.Batch075
import WildNumber.FiniteCertificates.Batch076
import WildNumber.FiniteCertificates.Batch077

namespace WildNumber.Nine.Census
set_option maxRecDepth 12000
theorem all_representatives : ∀ g ∈ repMasks, ∀ B, ¬ NumericModel g B := by
  have h : ∀ batch ∈ repBatches, ∀ g ∈ batch, ∀ B, ¬ NumericModel g B :=
    checkedCons checked000 (checkedCons checked001 (checkedCons checked002 (checkedCons checked003 (checkedCons checked004 (checkedCons checked005 (checkedCons checked006 (checkedCons checked007 (checkedCons checked008 (checkedCons checked009 (checkedCons checked010 (checkedCons checked011 (checkedCons checked012 (checkedCons checked013 (checkedCons checked014 (checkedCons checked015 (checkedCons checked016 (checkedCons checked017 (checkedCons checked018 (checkedCons checked019 (checkedCons checked020 (checkedCons checked021 (checkedCons checked022 (checkedCons checked023 (checkedCons checked024 (checkedCons checked025 (checkedCons checked026 (checkedCons checked027 (checkedCons checked028 (checkedCons checked029 (checkedCons checked030 (checkedCons checked031 (checkedCons checked032 (checkedCons checked033 (checkedCons checked034 (checkedCons checked035 (checkedCons checked036 (checkedCons checked037 (checkedCons checked038 (checkedCons checked039 (checkedCons checked040 (checkedCons checked041 (checkedCons checked042 (checkedCons checked043 (checkedCons checked044 (checkedCons checked045 (checkedCons checked046 (checkedCons checked047 (checkedCons checked048 (checkedCons checked049 (checkedCons checked050 (checkedCons checked051 (checkedCons checked052 (checkedCons checked053 (checkedCons checked054 (checkedCons checked055 (checkedCons checked056 (checkedCons checked057 (checkedCons checked058 (checkedCons checked059 (checkedCons checked060 (checkedCons checked061 (checkedCons checked062 (checkedCons checked063 (checkedCons checked064 (checkedCons checked065 (checkedCons checked066 (checkedCons checked067 (checkedCons checked068 (checkedCons checked069 (checkedCons checked070 (checkedCons checked071 (checkedCons checked072 (checkedCons checked073 (checkedCons checked074 (checkedCons checked075 (checkedCons checked076 (checkedCons checked077 (by simp))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  intro g hg
  obtain ⟨xs,hxs,hg⟩ := List.mem_flatten.mp (show g ∈ repBatches.flatten by simpa [repMasks] using hg)
  exact h xs hxs g hg
end WildNumber.Nine.Census
