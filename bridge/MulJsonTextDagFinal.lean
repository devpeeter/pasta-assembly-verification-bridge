-- Candidate generated mechanically from generated/mul-check.json; checked readback follows.
import MulJsonTextDagBase

namespace PastaBridge.MulJsonTextDag

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option pp.maxSteps 1000
set_option pp.deepTerms false

theorem retained_value_readback : retainedMultiplicationArtifactValue = value_124 := by
  delta retainedMultiplicationArtifactValue value_124 value_123 value_122 value_121 value_120 value_119 value_118 value_117 value_116 value_115 value_114 value_113 value_112 value_111 value_110 chunk_110_0 chunk_110_1 chunk_110_2 chunk_110_3 chunk_110_4 chunk_110_5 chunk_110_6 chunk_110_7 chunk_110_8 chunk_110_9 chunk_110_10 chunk_110_11 chunk_110_12 chunk_110_13 chunk_110_14 chunk_110_15 chunk_110_16 chunk_110_17 chunk_110_18 chunk_110_19 chunk_110_20 chunk_110_21 chunk_110_22 chunk_110_23 chunk_110_24 chunk_110_25 chunk_110_26 chunk_110_27 chunk_110_28 value_109 value_108 value_107 value_106 value_105 value_104 value_103 value_102 value_101 value_100 value_99 value_98 value_97 value_96 value_95 value_94 value_93 value_92 value_91 value_90 value_89 value_88 value_87 value_86 value_85 value_84 value_83 value_82 value_81 value_80 value_79 value_78 value_77 value_76 value_75 value_74 value_73 value_72 value_71 value_70 value_69 value_68 value_67 value_66 value_65 value_64 value_63 value_62 value_61 value_60 value_59 value_58 value_57 value_56 value_55 value_54 value_53 value_52 value_51 value_50 value_49 value_48 value_47 value_46 value_45 value_44 value_43 value_42 value_41 value_40 value_39 value_38 value_37 value_36 value_35 value_34 value_33 value_32 value_31 value_30 value_29 value_28 value_27 value_26 value_25 value_24 value_23 value_22 value_21 value_20 value_19 value_18 value_17 value_16 value_15 value_14 value_13 value_12 value_11 value_10 value_9 value_8 value_7 value_6 value_5 value_4 value_3 value_2 value_1 value_0
  rfl

attribute [local irreducible] retainedMultiplicationArtifactBytes

theorem retained_bytes_readback :
    StringBytes.bytes (text_124 ++ "\n") = retainedMultiplicationArtifactBytes := by
  have checked : (StringBytes.bytes (text_124 ++ "\n") ==
      retainedMultiplicationArtifactBytes) = true := by
    simp only [↓StringBytes.append, ↓StringBytes.intercalate,
      List.map_cons, List.map_nil, List.map_append,
      ↓List.append_assoc,
      List.intercalate_cons_cons, List.intercalate_singleton,
      ↓text_0, ↓text_1, ↓text_2, ↓text_3, ↓text_4, ↓text_5, ↓text_6, ↓text_7, ↓text_8, ↓text_9, ↓text_10, ↓text_11, ↓text_12, ↓text_13, ↓text_14, ↓text_15, ↓text_16, ↓text_17, ↓text_18, ↓text_19, ↓text_20, ↓text_21, ↓text_22, ↓text_23, ↓text_24, ↓text_25, ↓text_26, ↓text_27, ↓text_28, ↓text_29, ↓text_30, ↓text_31, ↓text_32, ↓text_33, ↓text_34, ↓text_35, ↓text_36, ↓text_37, ↓text_38, ↓text_39, ↓text_40, ↓text_41, ↓text_42, ↓text_43, ↓text_44, ↓text_45, ↓text_46, ↓text_47, ↓text_48, ↓text_49, ↓text_50, ↓text_51, ↓text_52, ↓text_53, ↓text_54, ↓text_55, ↓text_56, ↓text_57, ↓text_58, ↓text_59, ↓text_60, ↓text_61, ↓text_62, ↓text_63, ↓text_64, ↓text_65, ↓text_66, ↓text_67, ↓text_68, ↓text_69, ↓text_70, ↓text_71, ↓text_72, ↓text_73, ↓text_74, ↓text_75, ↓text_76, ↓text_77, ↓text_78, ↓text_79, ↓text_80, ↓text_81, ↓text_82, ↓text_83, ↓text_84, ↓text_85, ↓text_86, ↓text_87, ↓text_88, ↓text_89, ↓text_90, ↓text_91, ↓text_92, ↓text_93, ↓text_94, ↓text_95, ↓text_96, ↓text_97, ↓text_98, ↓text_99, ↓text_100, ↓text_101, ↓text_102, ↓text_103, ↓text_104, ↓text_105, ↓text_106, ↓text_107, ↓text_108, ↓text_109, ↓text_110, ↓text_111, ↓text_112, ↓text_113, ↓text_114, ↓text_115, ↓text_116, ↓text_117, ↓text_118, ↓text_119, ↓text_120, ↓text_121, ↓text_122, ↓text_123, ↓text_124,
      texts_chunk_110_0, texts_chunk_110_1, texts_chunk_110_2, texts_chunk_110_3, texts_chunk_110_4, texts_chunk_110_5, texts_chunk_110_6, texts_chunk_110_7, texts_chunk_110_8, texts_chunk_110_9, texts_chunk_110_10, texts_chunk_110_11, texts_chunk_110_12, texts_chunk_110_13, texts_chunk_110_14, texts_chunk_110_15, texts_chunk_110_16, texts_chunk_110_17, texts_chunk_110_18, texts_chunk_110_19, texts_chunk_110_20, texts_chunk_110_21, texts_chunk_110_22, texts_chunk_110_23, texts_chunk_110_24, texts_chunk_110_25, texts_chunk_110_26, texts_chunk_110_27, texts_chunk_110_28]
    all_goals decide +kernel
  exact eq_of_beq checked

theorem retained_encoding :
    (JsonEncoding.documentText 64 retainedMultiplicationArtifactValue).map StringBytes.bytes =
      .ok retainedMultiplicationArtifactBytes := by
  rw [JsonEncoding.documentText, retained_value_readback, encoded_124]
  change Except.ok _ = Except.ok _
  exact congrArg Except.ok retained_bytes_readback

#print axioms retained_value_readback
#print axioms retained_bytes_readback
#print axioms retained_encoding

end PastaBridge.MulJsonTextDag
