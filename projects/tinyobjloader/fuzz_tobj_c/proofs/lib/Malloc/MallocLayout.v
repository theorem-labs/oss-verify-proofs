(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "True"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "ltb"; "leb"; "modulo"; "pow"; "div"; "of_nat"; "shiftr"; "sub"; "eqb"; "max"; "min"; "to_nat"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "bool"; "true"; "Some"; "option"; "prod"; "snd"; "fst"; "andb"; "pair"; "nil"; "app"; "false"; "None"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "region"; "rg_len"; "rkind"; "size_classes"; "sptr"; "znth"; "RkMetaRes"; "rg_kind"; "size_to_class"; "brkst"; "rg_live"; "IB"; "MMAP_THRESHOLD"; "UNIT"; "class_of_units"; "rg_rw"; "BrkCur"; "RkMap"; "astate"; "class_size"; "initial_cnt"; "prid"; "st_brk"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "holds"; "topL"; "units_of"; "wz"; "fits"; "range_in_maps"; "addr_of"; "byteview_of"; "ctz_tab_bytes"; "mc_img_hi"; "mc_img_lo"; "mc_lock"; "MC"; "class_ok_units"; "mc_auxv"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_med_cnt_tab"; "mc_need_locks"; "mc_page_size"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "med_cnt_tab_bytes"; "nested_host_classes"; "nests_into"; "size_classes_bytes"; "small_cnt_tab_bytes"; "vm_ok"; "wdisj"; "wok_of_mem"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "ly_reg"; "zseq"; "LMem"; "layout"; "region_of"; "loc"; "ly_top"; "loc_addr"; "alloc_owned"; "footprint"; "le_byte"; "ly_brk0"; "ly_sec"; "repr"; "user_blocks"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "alloc_top"; "vm_maps"; "VmMaps"; "vm_brk"; "vm_noaccess"; "vm_reserved"; "vm_start_brk"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Notation aceil_lo := 140735332483072%Z.
Notation aceil_hi := 140737479966720%Z.
Definition topL (L : layout) : Z := ltac2:(tb__ "0|0|
S14Z7fff7f800000S15S6aVL;A1Z7fffff800000A2A2").
Lemma topL_range : ltac2:(tb__ "0|1|
S67S1S8Z7fff7f800000S43R1A1M0A2S8G0Z7fffff800000A2A2FL;").
Proof. intros L. unfold topL. lia. Qed.
Lemma topL_val : ltac2:(tb__ "0|1|
S67S1S8Z7fff7f800000S43R1A1M0A2S8G0Z7fffff800000A2A2FL;").
Proof. exact topL_range. Qed.
Lemma topL_of_range : ltac2:(tb__ "0|1|
S67S1S8Z7fff7f800000S6aR1A1M0A2S8G0Z7fffff800000A2A2S2S0S43R2A1S6aR2A1A3F_;FL;").
Proof. intros L H. unfold topL in *. lia. Qed.

Ltac top_range_of L :=
  lazymatch goal with
  | _ : 0x7fff7f800000 <= topL L <= 0x7fffff800000 |- _ => fail
  | _ => pose proof (topL_val L)
  end.
Ltac top_ranges :=
  repeat match goal with
         | |- context [topL ?L] => top_range_of L
         | _ : context [topL ?L] |- _ => top_range_of L
         end.

Definition class_usable (c : Z) : Z := class_size c - IB.

Definition fits (c n : Z) : bool := n <=? class_usable c.

Definition units_of (n : Z) : Z := ltac2:(tb__ "0|0|
S11S12S7Vn;S33A2Z1A2Z4A2").

Lemma units_of_div : ltac2:(tb__ "0|0|
S0S8Z0R1A2S2S0S44R2A1SfS7R2Z3A2Z10A2A3F_;Fn;").
Proof.
  intros n Hn. unfold units_of, IB. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 4) with 16. f_equal. lia.
Qed.

Lemma size_to_class_units : ltac2:(tb__ "0|0|
S0S2S0S30R1A1S36S44R1A1A1A3Fn;").
Proof. reflexivity. Qed.

Lemma fits_units : ltac2:(tb__ "0|0|
S0S0S8Z0R1A2S2S19S46R3R2A2ScS7S44R2A1Z1A2S2dR3S2bA2A2A3F_;Fn;Fc;").
Proof.
  intros c n Hn. unfold fits, class_usable, class_size, UNIT, IB.
  rewrite units_of_div by lia.
  set (s := znth c size_classes).
  destruct (n <=? 16 * s - 4) eqn:E1; destruct ((n + 3) / 16 + 1 <=? s) eqn:E2; auto.
  - apply Z.leb_le in E1. apply Z.leb_gt in E2. exfalso.
    assert ((n + 3) / 16 < s) by (apply Z.div_lt_upper_bound; lia). lia.
  - apply Z.leb_gt in E1. apply Z.leb_le in E2. exfalso.
    assert (s <= (n+3) / 16) by lia.
    assert (16 * ((n + 3) / 16) <= n + 3) by (apply Z.mul_div_le; lia). lia.
Qed.

Definition class_ok_units (k : Z) : bool := ltac2:(tb__ "0|3|
S36Vk;A1S0S20S20S20ScZ0M0R1A2SbR1Z30A2A2ScS7Vk;Z1A2M1S2dR1S2bA2M2A2A2S63S0S0SbG2G1A2Lc';S65G0R1A2A3A2Tc;").

Lemma class_ok_units_all : ltac2:(tb__ "0|0|
S2S19S63S0S4fS65Z0Z1fffA2A3S1aA3").
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_zseq_at : ltac2:(tb__ "0|0|
S0S19F_;S0S0S0S2S19S63S0R4S65R3R2A2A3S1aA3S8Z0R3A2S1S8R5R3A2S9R3S7R5R4A2A2A2S2S19R7R4A1S1aA3F_;F_;F_;Fk;Fn;Flo;Ff;").
Proof.
  intros f lo n k H Hn Hk. unfold zseq in H.
  rewrite forallb_forall in H.
  apply H. apply in_map_iff. exists (Z.to_nat (k - lo)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma units_bound : ltac2:(tb__ "0|2|
S0S1S8Z0M0R1A2S9R1S34A2A2S1S8G0S44R2A1M1A2S9G1Z1fffA2A2F_;Fn;").
Proof.
  intros n Hn. unfold MMAP_THRESHOLD in Hn. rewrite units_of_div by lia.
  split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia.
Qed.

Theorem size_to_class_spec : ltac2:(tb__ "0|3|
S0S1S8Z0M0R1A2M1S9R1S34A2A2S1S1S8G0S30R2A1M2A2S9G2Z30A2A2S1S2S19S46G2R2A2S1aA3S0S1G1S9R1S30R3A1A2A2S2S19S46R2R4A2S24A3F_;Fc;A2A2F_;Fn;").
Proof.
  intros n Hn.
  pose proof (units_bound n Hn) as Hk.
  pose proof (forallb_zseq_at _ _ _ (units_of n) class_ok_units_all ltac:(lia) ltac:(lia)) as H.
  unfold class_ok_units in H. rewrite size_to_class_units.
  set (c := class_of_units (units_of n)) in *.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  split; [lia|]. split.
  - rewrite fits_units by lia. exact H3.
  - intros c' Hc'. rewrite fits_units by lia.
    pose proof (forallb_zseq_at _ _ _ c' H4 ltac:(lia) ltac:(lia)) as H5.
    apply Z.ltb_lt in H5. apply Z.leb_gt. lia.
Qed.

Lemma size_classes_increasing : ltac2:(tb__ "0|0|
S2S19S63S0S0SbS2dR1S2bA2S2dS7R1Z1A2S2bA2A2Lc;S65Z0Z2fA2A3S1aA3").
Proof. vm_compute. reflexivity. Qed.

Lemma size_classes_pos : ltac2:(tb__ "0|1|
S2S19S63S0S0SbZ0M0S2dR1S2bA2A2Lc;S65G0Z30A2A3S1aA3").
Proof. vm_compute. reflexivity. Qed.

Lemma class_usable_max : class_usable 47 = 131052.
Proof. reflexivity. Qed.

Definition nested_host_classes : list Z := ltac2:(tb__ "0|0|
S17S0ZfS17S0Z13S17S0Z17S22S0A1A3A3A3").

Definition nests_into (sc j : Z) : Prop := ltac2:(tb__ "0|1|
S3S0S0S1S8Z0R1A2S3cVsc;R1A2S0S1S8S7SaS3bVsc;A1M0R1A2S35A2SfS27Z2A2A2S2S0Vj;S30S12S7S35SaR1G0A2A2S33A2A1A3A2Tcnt;A2Lusage;A2").

Definition nested_hosts_stmt : Prop := ltac2:(tb__ "0|0|
S0S0S1S8Z0R2A2S9R2Z30A2A2S5cR3R2A2S1S62S0R3S5bA3S9R4R3A2A2F_;F_;Fj;Fsc;").

Record mconsts := MC {
  mc_malloc_pc : Z;
  mc_malloc_impl : Z;
  mc_free_pc : Z;
  mc_free_impl : Z;
  mc_calloc_pc : Z;
  mc_get_meta : Z; mc_nontrivial_free : Z; mc_alloc_meta : Z; mc_alloc_slot : Z;
  mc_enframe : Z; mc_allzerop : Z;
  mc_mmap : Z; mc_mprotect : Z; mc_munmap : Z; mc_syscall_ret : Z; mc_errno_location : Z;
  mc_memset : Z; mc_memcpy : Z; mc_stack_chk_fail : Z;
  mc_ctx : Z;
  mc_lock : Z;
  mc_replaced : Z;
  mc_libc : Z;
  mc_chk_guard : Z;
  mc_chk_guard_got : Z;
  mc_tp : Z;
  mc_size_classes : Z; mc_small_cnt_tab : Z; mc_med_cnt_tab : Z; mc_ctz_tab : Z;
  mc_img_lo : Z; mc_img_hi : Z
}.

Definition C_P : mconsts :=
  MC 0x1fe2c 0x207bc 0x1fcec 0x1fe30 0x1fbb4
     0x1fffc 0x2010c 0x204e4 0x20b2c 0x213d0 0x21520
     0x2169c 0x21788 0x217d0 0x1fb70 0x1fba8
     0x26f98 0x26b94 0x1fb68
     0x59c90 0x59c88 0x5a030 0x59c18 0x59bf8 0x28610 0x39990
     0x1097c 0x109dc 0x109f7 0x1095c
     0x10000 0x5b000.

Definition C_U : mconsts := ltac2:(tb__ "0|1|
S4eS7Z1fe2cZ740M0A2S7Z207bcG0A2S7Z1fcecG0A2S7Z1fe30G0A2S7Z1fbb4G0A2S7Z1fffcG0A2S7Z2010cG0A2S7Z204e4G0A2S7Z20b2cG0A2S7Z213d0G0A2S7Z21520G0A2S7Z2169cG0A2S7Z21788G0A2S7Z217d0G0A2S7Z1fb70G0A2S7Z1fba8G0A2S7Z26f98G0A2S7Z26b94G0A2S7Z1fb68G0A2Z5a3d0Z5a3c8Z5a770Z5a358Z5a338Z28d50Z3a0d0Z108ecZ1094cZ10967Z108ccZ10000Z5b000A20").

Definition mc_errno (C : mconsts) : Z := mc_tp C - 164.
Definition mc_need_locks (C : mconsts) : Z := mc_libc C + 3.
Definition mc_auxv (C : mconsts) : Z := mc_libc C + 8.
Definition mc_page_size (C : mconsts) : Z := mc_libc C + 48.

Example errno_P : mc_errno C_P = 0x398ec. Proof. reflexivity. Qed.
Example errno_U : mc_errno C_U = 0x3a02c. Proof. reflexivity. Qed.

Definition malloc_stack : Z := 768.
Definition calloc_stack : Z := 800.
Definition free_stack : Z := 464.
Definition malloc_stack_max : Z := 48 + 48 * 144 + 144.

Definition u16le (z : Z) : list Z := ltac2:(tb__ "0|1|
S17S0SdVz;Z100M0A2S17S0SdSfVz;G0A2G0A2S22S0A1A3A3").
Definition size_classes_bytes : list Z := flat_map u16le size_classes.
Definition small_cnt_tab_bytes : list Z := concat small_cnt_tab.
Definition med_cnt_tab_bytes : list Z := med_cnt_tab.
Definition ctz_tab_bytes : list Z := ltac2:(tb__ "0|0|
S17S0Z0S17S0Z1S17S0Z1cS17S0Z2S17S0Z1dS17S0ZeS17S0Z18S17S0Z3S17S0Z1eS17S0Z16S17S0Z14S17S0ZfS17S0Z19S17S0Z11S17S0Z4S17S0Z8S17S0Z1fS17S0Z1bS17S0ZdS17S0Z17S17S0Z15S17S0Z13S17S0Z10S17S0Z7S17S0Z1aS17S0ZcS17S0Z12S17S0Z6S17S0ZbS17S0Z5S17S0ZaS17S0Z9S22S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma ctz_tab_ok : ltac2:(tb__ "0|2|
S2S19S63S0S0S13S74S0S16S11SdSaSeZ2M0R1A2Z77cb531A2SeG0Z20M1A2A2Z1bA2A1S4aZ63A4R1A2Lk;S65Z0G1A2A3S1aA3").
Proof. vm_compute. reflexivity. Qed.

Lemma size_classes_bytes_length : length size_classes_bytes = 96%nat.
Proof. reflexivity. Qed.

Definition byteview_of (rd : word -> option byte) (wok : word -> bool) : byteview := ltac2:(tb__ "0|5|
S0S19S1cS0A1M0L_;S20S20ScZ0R1A2SbR1SeZ2Z40A2A2A2Vwok;S41Q40R1A2M1A1A2S1cS40Q8M2A1M3A1G0Lx;Vrd;G1A1G3S1bS0S3fG2R1A2A2Lb;S25S0A1M4X1cx2G4X19x2Lz;").

Definition wok_of_mem (mem : word -> option byte) : word -> bool := ltac2:(tb__ "0|1|
S40Q40A1S1cS40Q8A1M0A1S19Lx;Vmem;R1A1G0S1aLb;S24X1cx2La;").

Definition byteview_of_mem (mem : word -> option byte) : byteview := ltac2:(tb__ "0|0|
S49Vmem;S61Vmem;A1A2").

Definition repr_w (L : layout) (s : astate) (rd : word -> option byte) (wok : word -> bool) : Prop := ltac2:(tb__ "0|0|
S71VL;Vs;S49Vrd;Vwok;A2A3").

Definition addr_of (L : layout) (p : sptr) : Z := ltac2:(tb__ "0|0|
S6bVL;S66Vp;A1A2").

Definition blocks (L : layout) (s : astate) : list (Z * Z) := ltac2:(tb__ "0|1|
S75S1dS2cS0A2M0S1dS0S0A2G0S21S0S0S48VL;S1fS2cS0R1A3A2S1eS2cS0R1A3A4Lb;S72Vs;A1A4").

Definition owned (C : mconsts) (L : layout) (s : astate) (a : Z) : Prop := ltac2:(tb__ "0|1|
S4S6cVL;Vs;Va;A3S1S8S4dVC;A1M0Va;A2S9Va;S7G0Z4A2A2A2A2").

Definition wz (z : Z) : word := Z_to_bv 64 z.

Definition range_in_maps (maps : list (word * word)) (a n : Z) : Prop := ltac2:(tb__ "0|4|
S3S1dS40Q40M0A1M1G1A2M2G2S1S62G2R1Vmaps;A3S1S8S3fG0S1fG1G1R1A3A2M3Va;A2S8S7Va;Vn;A2S7G3S3fG0S1eG1G1R1A3A2A2A2A2A2Le;A2").

Definition vm_ok (L : layout) (s : astate) (vm : VmMaps) : Prop := ltac2:(tb__ "0|21|
S1S18S28S2S1cS28A1M0S68Vs;R2A2S1bS28R1A2A3M1S2S19S32R2A1S1aA3M2S2S2aS2fR3A1M3S39A3M4S62S1dS40Q40M5A1M6G6A2M7S21G6G6S45S64VL;R5A2A1S45S29R4A1A1A4S77Vvm;A1M8A3F_;F_;F_;Frg;Fr;S1S18S28G1S2S2aS2fR2A1S2eA3S1S62G7S21G6G6S45S64VL;R4A2M9A1S45S29R3A1MaA1A4G8A3S1S0S8Z1MbR1A2McS8SaS27S7R2GbA2A2S29R5A1MdA2S5S62S0SaS27R3A2S37R6A1A3A1S47S7aVvm;A1MeS7S64VL;R8A2MfSaS27R4A2A2S27A3F_;F_;F_;Fk;S0S62S0R1S37R4A1M10A3G7S62G7R1GeA3S4S8S7S7GfR4A2M11S27A2S3fG5S1fG6G6R2A3A2M12A2S8S7G12S3fG5S1eG6G6R2A3A2A2G11A2A2F_;Fe;F_;Foff;A2A2F_;F_;Frg;Fr;S1S31OLx;S3eVs;A1M13S1S2S0S3fG5S79Vvm;A1A2M14S6fVL;A1M15A3S1S2S0S3fG5S7cVvm;A1A2G15A3M16S2S0SdG15S27A2Z0A3A2A2S6S18S0S1S2S0S64VL;R2A2G15A3S1S2S0G14S7G15SaS27R1A2A2A3S1G16S0S1GcS9R1R2A2A2S47G8S7G15SaS27R2A2A2S27A3F_;Fk;A2A2A2Lpages;Lr;X31x3S1S2cS0S62S1dS69S0A2M17S21S69S0S66R2A1R1A4S6dVs;A1M18A3S47G8S48VL;R3A2R2A3F_;Fn;Fp;S1S18S28S0S2G0S68Vs;R3A2S1bS28R2A2A3M19S2S2aG3S2eA3S62S0R3G10A3S1S8S27R4A2S8S7R4S27A2GdA2A2F_;F_;F_;Foff;Frg;Fr;S1S18S18S28S28S5S2S18R4R3A3A1S2G0S68Vs;R5A2S1bS28R3A2M1aA3M1bG1bS2S2aS2fR5A1S2eA3M1cG1cS4S8S7S64VL;R9A2M1dS29R7A1A2GfA2S8S7GfS29R6A1A2G1dA2A2F_;F_;F_;F_;F_;Frg2;Frg1;Fr2;Fr1;S1S18S28G1G2S8S27GaA2F_;F_;Frg;Fr;S1S18S28G1G2S1S8S27G9A2S8S7G9GaA2S43VL;A1M1eA2A2F_;F_;Frg;Fr;S1S18S28S2cS0S2G0S68Vs;R4A2G1aA3S2S2aS2fR4A1S2eA3S2S19S32R5A1S1aA3S62G17S21S69S0S66R5A1R4A4G18A3S5S2S18S3dR6A1R8A3A1S4S8S7S6bVL;S66R7A1A2M1fR6A2G1dA2S8S7G1dS29R8A1A2G1fA2A2F_;F_;F_;F_;F_;Fn;Fq;Frg;Fr;S1S18S0S18S28S2S31G13S38R4R3A2A3G19G4S2S19S32R4A1S1aA3S4S8S7S64VL;R6A2M20GdA2S7GfS27A2A2S8S7GfSaS27R7A2A2G20A2A2F_;F_;F_;F_;Frgk;Fk;Fp;Fr;S2S0G1eS76Vvm;A1A3A2A2A2A2A2A2A2A2A2A2").

Lemma vm_ok_top : ltac2:(tb__ "0|0|
S67S3aS78S5fR3R2R1A3S2S0S43R4A1S76R2A1A3F_;Fvm;Fs;FL;").
Proof. intros L s vm H. do 10 (apply proj2 in H). exact H. Qed.

Definition ledger_ok (C : mconsts) (vm : VmMaps) : Prop := ltac2:(tb__ "0|5|
S1dS40Q40M0A1M1G1A2M2S62G2R1S77Vvm;A1A3S1S8S27S3fG0S1fG1G1R2A3A2M3A2S1S8S7G3S3fG0S1eG1G1R2A3A2A2M4S76Vvm;A1A2S4S8G4S4cVC;A1A2S8S4bVC;A1G3A2A2A2A2F_;Fe;").

Definition img_reserved (C : mconsts) (vm : VmMaps) : Prop := ltac2:(tb__ "0|4|
S0S1S8S4cVC;A1R1A2S9R1S4bVC;A1A2A2S3S1dS40Q40M0A1M1G1A2M2G2S1S62G2R1S7bVvm;A1A3S1S8S3fG0S1fG1G1R1A3A2M3R3A2S9R3S7G3S3fG0S1eG1G1R1A3A2A2A2A2A2Le;A2F_;Fx;").

Definition wdisj (e e' : word * word) : Prop := ltac2:(tb__ "0|4|
S4S8S7S3fQ40M0S1fS40G0A1M1G1Ve;A3A2M2S3fG0S1eG1G1Ve;A3A2A2S3fG0S1fG1G1Ve';A3A2M3A2S8S7G3S3fG0S1eG1G1Ve';A3A2A2G2A2A2").
Definition mwf (l : list (word * word)) : Prop := ltac2:(tb__ "0|4|
S26S1dS40Q40M0A1M1G1A2M2A1M3G2G3S2G3Vl;S23G2R3S17G2R2R1A3A3A3S1S9Z0S3fG0S1eG1G1R3A3A2A2G2S62G2R1S23G2R5R3A3A3S60R5R2A2F_;Fe';A2F_;Fl2;Fe;Fl1;").
Definition maps_wf (vm : VmMaps) : Prop := mwf (vm_maps vm).

Definition holds (m : byteview) (a : Z) (w : nat) (v : Z) : Prop := ltac2:(tb__ "0|0|
S18S73R1Vw;A2S2S1cS0A1Vm;S7Va;S10R2A1A2A1S1bS0S6eVv;Vw;R2A3A2A3F_;Fk;").

Definition statics_ok (C : mconsts) (rv wv : byteview) : Prop := ltac2:(tb__ "0|6|
S1S42Vrv;S55VC;A1U1Z0M0A4S1S42Vrv;S56VC;A1U8M1Z1000A4S1S42Vrv;S57VC;A1U4M2G0A4S1S42Vwv;S4dVC;A1G2G0A4S1S18S73R1U60A2S2S1cS0A1M3Vrv;S7S58VC;A1S10R2A1M4A2A1S1bS0S74S0R2S5dG0A4A2A3F_;Fk;S1S18S73R1U1bA2S2G3Vrv;S7S59VC;A1G4A2A1S1bS0S74S0R2S5eG0A4A2A3F_;Fk;S1S18S73R1G2A2S2G3Vrv;S7S54VC;A1G4A2A1S1bS0S74S0R2S5aG0A4A2A3F_;Fk;S1S18S73R1U20A2S2G3Vrv;S7S53VC;A1G4A2A1S1bS0S74S0R2S4aG0A4A2A3F_;Fk;S3S0S0S1S42Vrv;S52VC;A1G1S51VC;A1M5A4S42Vrv;G5G1R1A4A2Lg;A2A2A2A2A2A2A2A2A2").

Definition auxv_ok (C : mconsts) (L : layout) (rv : byteview) : Prop := ltac2:(tb__ "0|b|
S3S0S0S3S0S0S3S0S0S1S42Vrv;S50VC;A1U8M0R3A4S1S42Vrv;S7R3SaZ10M1R1A2M2A2M3G0Z19M4A4S1S42Vrv;S7G3Z8M5A2G0R2A4S1S42Vrv;S7R2G5A2G0S70VL;A1A4S1S0S1S8Z0M6R1A2M7S9R1R2A2M8A2S3S0S0S3S0S0S1S42Vrv;S7R7SaG1R4A2A2M9G0R2A4S1S5S2S0R2G6A3A1S1S42Vrv;S7G9G5A2G0R1A4S2S0R2G4A3S3S0S0S42Vrv;S7R3G5A2G0R1A4Lw;A2F_;A2A2A2Lv;A2Lk;A2F_;Fi;S1S3S0S0S1S9R2R1A2S1S42Vrv;S7R4G2A2G0G6A4S0S1S9R3R1A2G8A2S3S0S0S1S42Vrv;S7R7SaG1R3A2A2G0R1A4S1S5S2S0R1G6A3A1S5S2S0R1G4A3A1A2A2Lk;A2F_;Fi;A2A2Lt;A2S1S8S43VL;A1MaR3A2S1S8GaR2A2S1S8S7R2G1A2SeZ2Z40A2A2G7A2A2A2A2A2A2A2A2A2Ln;A2Lq;A2Lav;A2").
