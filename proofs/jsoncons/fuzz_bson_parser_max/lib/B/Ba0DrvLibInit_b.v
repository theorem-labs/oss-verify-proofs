(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefPrintfLib
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvStdio_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Definition LIBINIT_KN : list kentry :=
  [KImg 65536 1282048; KImg 6759057 6759060; KImg 6759061 6765616; KImg 1293304 1293472; KImg 6897608 6897656;      (* [comment removed for export] *)
   KWord (SA (ELit 0) 6896960) 8 (EVar 3); KWord (SA (ELit 0) 6765624) 8 (ELit 6765624); KWord (SA (ELit 0) 6765656) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 6765808) 8 (EVar 3); KWord (SA (ELit 0) 6765776) 8 (ELit 6897608); KWord (SA (ELit 0) 6897560) 8 (EAlu ALU_ADD (EVar 1) (ELit (-160)));
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 6896976) 1 (ELit 0); KWord (SA (ELit 0) 6896980) 4 (ELit 0); KWord (SA (ELit 0) 6896984) 4 (ELit 2); KWord (SA (ELit 0) 6896992) 8 (ELit 6897000);
   KWord (SA (ELit 0) 6897000) 8 (ELit 0); KWord (SA (ELit 0) 6897008) 8 (ELit 1148964); KWord (SA (ELit 0) 6897264) 8 (ELit 619876);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 6897016) 8 (ELit 1148964); KWord (SA (ELit 0) 6897272) 8 (ELit 687916);
   KWord (SA (ELit 0) 6897555) 1 (ELit 0); KWord (SA (ELit 0) 6897776) 4 (ELit 0)].
(* [comment removed for export] *)
Definition LIBINIT_IMG : list (Z * Z) := [(65536, 1282048); (6759057, 6759060); (6759061, 6765616); (1293304, 1293472); (6897608, 6897656)].

(* [comment removed for export] *)
Definition INIT_CELLS_A : list (Z * Z * Z) :=
  [(6896976, 1, 0); (6896980, 4, 0); (6896984, 4, 2); (6896992, 8, 6897000); (6897000, 8, 0); (6897008, 8, 1148964); (6897264, 8, 619876);
   (6897555, 1, 0); (6897776, 4, 0); (6897016, 8, 1148964); (6897272, 8, 687916)].

(* [comment removed for export] *)
Record drv_lib_cellsA (Lay : lib_layoutA) : Prop := DRV_LIB_CELLSA {
  dlc_td_self : lla_td_self Lay = 0x673c38;  dlc_td_tid : lla_td_tid Lay = 0x673c58;  dlc_td_canary : lla_td_canary Lay = 0x673cf0;
  dlc_td_locale : lla_td_locale Lay = 0x673cd0;  dlc_locale : lla_locale Lay = 0x693fc8;  dlc_guard : lla_guard Lay = 0x693d40;
  dlc_auxvp : lla_auxvp Lay = 0x693f98;  dlc_phdr : lla_phdr Lay = 0x10040;  dlc_phent : lla_phent Lay = 56;  dlc_phnum : lla_phnum Lay = 11;
  dlc_init_img : forall iv, In iv (lla_init_img Lay) -> exists lo hi, In (lo, hi) LIBINIT_IMG /\ lo <= fst iv /\ snd iv <= hi;
  (* [comment removed for export] *)
  dlc_rw_lo : lla_rw_lo Lay <= 0x13bdb8;
  dlc_initc : forall iv, In iv (lla_initc Lay) -> 0 <= fst iv /\ snd iv <= 0x696000 /\ (snd iv <= 0x13bdb8 \/ 0x13bea0 <= fst iv) /\ (snd iv <= 0x694520 \/ 0x694920 <= fst iv)
                                                /\ (snd iv <= 0x672294 \/ 0x672295 <= fst iv);
  (* [comment removed for export] *)
  dlc_init_cells : lla_init_cells Lay = INIT_CELLS_A
}.

Lemma locale_imgA : forall k, (k < 6)%nat ->
  rdn ASEGS (fun _ => None) (Z_to_bv 64 (0x693fc8 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros k Hk. do 6 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibInit.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable M0 : word -> option byte.
  Variable Lay : lib_layoutA.
  Hypothesis LayL : lla_L Lay = L.
  Hypothesis DLC : drv_lib_cellsA Lay.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).

  Theorem lib_init_at_call : forall vals ebs kn LB LK cr A M (model : Model) (p0 : word),
    know_ok ASEGS (Env (vals_ev vals) ebs) (mrestrict (ahid A model) M) kn ->
    forallb (fun K => existsb (kentry_eqb K) kn) LIBINIT_KN = true ->
    vals_ev vals 1 = p0 ->
    dinvA LB LK cr A M model -> auxv_atA sp0 p0 M0 ->
    exists av uid rnd tid canary hw, lib_init_factsA Lay ar av uid rnd tid canary hw M.
  Proof.
    intros vals ebs kn LB LK cr A M model p0 HK HB P1 D (uidz & rnd & hwz & AW & AU & AH & AR1 & AR2 & AP & AP8).
    pose proof Hsp as Hsp'. set (E := Env (vals_ev vals) ebs) in *. set (MV := mrestrict (ahid A model) M) in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as (HOFF & _).
    rewrite forallb_forall in HB.
    assert (KB : forall K, In K LIBINIT_KN -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    assert (FULLR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M (Z_to_bv 64 a) n = Some bs)
      by (intros a n bs Hr; exact (rdn_of_mrestrict ASEGS _ M HOFF n _ bs Hr)).
    assert (NONE : forall lo hi, In (KImg lo hi) LIBINIT_KN -> hi <= 0x696000 -> forall i, 0 <= lo -> lo <= i < hi -> M (Z_to_bv 64 i) = None).
    { intros lo hi Hin Hhi i Hlo Hi. pose proof (kimg_clear E MV kn lo hi HK (KB _ Hin) i Hi) as X. unfold MV, mrestrict in X.
      rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ i D ltac:(lia)) in X. exact X. }
    assert (KW : forall a (w : nat) v, In (KWord (SA (ELit 0) a) w v) LIBINIT_KN -> 0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
                 rdn ASEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v))).
    { intros a w v Hin Ha Hw. apply FULLR. exact (kword_lit sp0 E MV kn a w v HK (KB _ Hin) Ha Hw). }
    pose proof (KW 6896960 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CG.
    pose proof (KW 6765624 8%nat (ELit 6765624) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CS.
    pose proof (KW 6765656 4%nat (EVar 4) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CT.
    pose proof (KW 6765808 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CC.
    pose proof (KW 6765776 8%nat (ELit 6897608) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CL.
    pose proof (KW 6897560 8%nat (EAlu ALU_ADD (EVar 1) (ELit (-160))) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CA.
    assert (TR : 1 <= bv_unsigned (vals_ev vals 4) <= 4194303).
    { pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold LIBINIT_KN; cbn [In]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev E] in X. exact X. }
    cbn [edenot ev E] in CG, CS, CT, CC, CL, CA. rewrite P1 in CA.
    assert (EA : alu64 ALU_ADD p0 (Z_to_bv 64 (-160)) = Z_to_bv 64 (bv_unsigned p0 - 160)).
    { rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
    rewrite EA in CA.
    set (av := bv_unsigned p0 - 160) in *.
    exists av, uidz, rnd, (bv_unsigned (vals_ev vals 4)), (bv_unsigned (vals_ev vals 3)), hwz.
    destruct DLC as [d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 dimg _ _ dcells].
    unfold lib_init_factsA. split.
    2:{ (* [comment removed for export] *)
      rewrite dcells, LayL, (dla_segs _ _ _ _ DL). unfold INIT_CELLS_A.
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6896976 1%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6896980 4%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6896984 4%nat (ELit 2) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6896992 8%nat (ELit 6897000) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6897000 8%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6897008 8%nat (ELit 1148964) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6897264 8%nat (ELit 619876) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6897555 1%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6897776 4%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6897016 8%nat (ELit 1148964) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6897272 8%nat (ELit 687916) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_nil. }
    unfold lib_init_facts. cbn [lib_view ll_heap heap_view HeapIface.hl_segs hl_sptop ll_init_img ll_td_self ll_td_tid ll_td_locale ll_locale ll_td_canary ll_guard ll_auxvp ll_init_cells].
    rewrite LayL, (dla_segs _ _ _ _ DL), (dla_sptop _ _ _ _ DL), d1, d2, d3, d4, d5, d6, d7. unfold cellz.
    rewrite !Z_to_bv_bv_unsigned.
    split. { intros iv a Hiv Ha. destruct (dimg iv Hiv) as (lo & hi & Hin & H1 & H2).
             unfold LIBINIT_IMG in Hin. cbn [In] in Hin.
             destruct Hin as [X|[X|[X|[X|[X|[]]]]]]; injection X as <- <-;
               [apply (NONE 65536 1282048) | apply (NONE 6759057 6759060) | apply (NONE 6759061 6765616) | apply (NONE 1293304 1293472) | apply (NONE 6897608 6897656)];
               first [lia | (unfold LIBINIT_KN; cbn [In]; tauto)]. }
    split; [exact CS|]. split; [exact CT|]. split; [lia|]. split; [exact CL|].
    split. { intros k Hk. apply (img_cell M _ 8%nat _ (locale_imgA k Hk)); [lia | cbn; lia|].
             intros i Hi. apply (NONE 6897608 6897656); [unfold LIBINIT_KN; cbn [In]; tauto | lia | lia | cbn in Hi; lia]. }
    split; [exact CC|]. split; [exact CG|]. split; [pose proof (bv_unsigned_in_range _ (vals_ev vals 3)) as X; change (bv_modulus 64) with (2 ^ 64) in X; lia|].
    split; [exact CA|]. split; [unfold av; lia|]. split; [unfold av; lia|].
    split. { unfold av. rewrite <- Zminus_mod_idemp_l, AP8. reflexivity. }
    split. { intros j Hj. unfold auxv_words. cbn [lib_view ll_phdr ll_phent ll_phnum]. rewrite d8, d9, d10.
             apply (rdn_tr M0 M _ 8%nat _ (AW j Hj)); [unfold av; lia | unfold av; cbn; lia|].
             intros i Hi. apply (di_above _ _ _ _ _ _ _ _ _ _ D). unfold av in *. cbn in Hi. lia. }
    repeat split; try lia. apply Forall_nil.      (* [comment removed for export] *)
  Qed.
End LibInit.
End FPX_1.
