(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 LibSym.

Module SegItab_Eu_1c0374.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(240064, 154%nat) ; (392112, 8%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_1c0374.

Module SegItab_Eu_2bbc6b.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(230216, 60%nat) ; (230476, 37%nat) ; (230624, 46%nat) ; (230808, 19%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_2bbc6b.

Module SegItab_Eu_314903.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(242560, 299%nat) ; (235648, 42%nat) ; (235816, 56%nat) ; (236040, 20%nat) ; (236144, 15%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_314903.

Module SegItab_Eu_33b84d.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(542560, 45%nat) ; (518476, 35%nat) ; (505388, 366%nat) ; (245448, 20%nat) ; (245528, 5%nat) ; (614184, 71%nat) ; (608100, 10%nat) ; (603156, 115%nat) ; (648640, 229%nat) ; (649556, 316%nat) ; (712664, 12%nat) ; (715928, 162%nat) ; (716576, 29%nat) ; (716768, 29%nat) ; (716884, 567%nat) ; (719952, 15%nat) ; (721212, 122%nat) ; (506852, 81%nat) ; (507176, 81%nat) ; (507500, 80%nat) ; (507820, 80%nat) ; (508140, 81%nat) ; (508464, 81%nat) ; (508788, 81%nat) ; (509112, 81%nat) ; (509436, 81%nat) ; (509760, 81%nat) ; (510084, 80%nat) ; (510404, 80%nat) ; (510724, 81%nat) ; (511048, 81%nat) ; (511372, 81%nat) ; (511696, 81%nat) ; (512020, 81%nat) ; (512344, 81%nat) ; (512668, 81%nat) ; (512992, 81%nat) ; (513316, 81%nat) ; (513640, 81%nat) ; (513964, 81%nat) ; (514288, 81%nat) ; (514612, 81%nat) ; (514936, 81%nat) ; (515260, 81%nat) ; (515584, 81%nat) ; (515908, 81%nat) ; (516232, 81%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_33b84d.

Module SegItab_Eu_38f9a9.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(222736, 98%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_38f9a9.

Module SegItab_Eu_4291a6.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(234848, 93%nat) ; (235220, 40%nat) ; (235380, 49%nat) ; (392328, 24%nat) ; (235648, 42%nat) ; (235816, 56%nat) ; (236040, 20%nat) ; (236144, 15%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_4291a6.

Module SegItab_Eu_4fc27e.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(241580, 131%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_4fc27e.

Module SegItab_Eu_53ab17.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(221424, 104%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_53ab17.

Module SegItab_Eu_649f1b.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(228520, 38%nat) ; (245448, 20%nat) ; (245528, 5%nat) ; (645012, 50%nat) ; (715928, 162%nat) ; (716576, 29%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_649f1b.

Module SegItab_Eu_65e49f.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(236204, 85%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_65e49f.

Module SegItab_Eu_8a1843.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(230216, 60%nat) ; (230476, 37%nat) ; (230624, 46%nat) ; (230808, 19%nat) ; (712712, 257%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_8a1843.

Module SegItab_Eu_8d3064.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(220680, 98%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_8d3064.

Module SegItab_Eu_8f1fe7.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(223808, 83%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_8f1fe7.

Module SegItab_Eu_a02991.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(221072, 88%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_a02991.

Module SegItab_Eu_a3bea9.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(240680, 73%nat) ; (392112, 8%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_a3bea9.

Module SegItab_Eu_aa48a8.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(234848, 93%nat) ; (235220, 40%nat) ; (235380, 49%nat) ; (392328, 24%nat) ; (235648, 42%nat) ; (235816, 56%nat) ; (236040, 20%nat) ; (236144, 15%nat) ; (712712, 257%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_aa48a8.

Module SegItab_Eu_aadf5d.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(237984, 341%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_aadf5d.

Module SegItab_Eu_bcdac2.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(242104, 66%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_bcdac2.

Module SegItab_Eu_bd4e09.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(217580, 58%nat) ; (392328, 24%nat) ; (219564, 46%nat) ; (372508, 28%nat) ; (372620, 50%nat) ; (219800, 90%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_bd4e09.

Module SegItab_Eu_c252e0.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(244980, 100%nat) ; (245380, 17%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_c252e0.

Module SegItab_Eu_c66d42.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(216812, 117%nat) ; (394048, 1%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_c66d42.

Module SegItab_Eu_cbd35e.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(240972, 152%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_cbd35e.

Module SegItab_Eu_ce2798.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(234164, 152%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_ce2798.

Module SegItab_Eu_dfe446.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(220220, 110%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_dfe446.

Module SegItab_Eu_e45441.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(228672, 94%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_e45441.

Module SegItab_Eu_e5699d.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(393464, 67%nat) ; (393740, 19%nat) ; (394184, 18%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_e5699d.

Module SegItab_Eu_ebd0b8.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(236568, 274%nat) ; (222064, 1%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_ebd0b8.

Module SegItab_Eu_ecf45c.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(371764, 118%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_ecf45c.

Module SegItab_Eu_edcba7.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(222284, 108%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_edcba7.

Module SegItab_Eu_f30027.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(243756, 306%nat) ; (235648, 42%nat) ; (235816, 56%nat) ; (236040, 20%nat) ; (236144, 15%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
End SegItab_Eu_f30027.
