(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefPrintfLib
  HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceA DrvKitA DrvNodesLazyK As0DrvKitA As0DrvEntry As0Drv_defs As0DrvLib As0DrvRead As0DrvStdio.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Definition LIBINIT_KN : list kentry :=
  [KImg 65536 880640; KImg 6357393 6357396; KImg 6357397 6360120; KImg 892736 892792; KImg 6492112 6492160;
   KWord (SA (ELit 0) 6491464) 8 (EVar 3); KWord (SA (ELit 0) 6360128) 8 (ELit 6360128); KWord (SA (ELit 0) 6360160) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 6360312) 8 (EVar 3); KWord (SA (ELit 0) 6360280) 8 (ELit 6492112); KWord (SA (ELit 0) 6492064) 8 (EAlu ALU_ADD (EVar 1) (ELit (-160)))].
(* [comment removed for export] *)
Definition LIBINIT_IMG : list (Z * Z) := [(65536, 880640); (6357393, 6357396); (6357397, 6360120); (892736, 892792); (6492112, 6492160)].

(* [comment removed for export] *)
Record drv_lib_cellsA (Lay : lib_layoutA) : Prop := DRV_LIB_CELLSA {
  dlc_td_self : lla_td_self Lay = 0x610c40;  dlc_td_tid : lla_td_tid Lay = 0x610c60;  dlc_td_canary : lla_td_canary Lay = 0x610cf8;
  dlc_td_locale : lla_td_locale Lay = 0x610cd8;  dlc_locale : lla_locale Lay = 0x630fd0;  dlc_guard : lla_guard Lay = 0x630d48;
  dlc_auxvp : lla_auxvp Lay = 0x630fa0;  dlc_phdr : lla_phdr Lay = 0x10040;  dlc_phent : lla_phent Lay = 56;  dlc_phnum : lla_phnum Lay = 11;
  dlc_init_img : forall iv, In iv (lla_init_img Lay) -> exists lo hi, In (lo, hi) LIBINIT_IMG /\ lo <= fst iv /\ snd iv <= hi;
  (* [comment removed for export] *)
  dlc_rw_lo : lla_rw_lo Lay <= 0xda090;
  dlc_initc : forall iv, In iv (lla_initc Lay) -> 0 <= fst iv /\ snd iv <= 0x633000 /\ (snd iv <= 0xda090 \/ 0xda178 <= fst iv) /\ (snd iv <= 0x631418 \/ 0x631818 <= fst iv)
                                                /\ (snd iv <= 0x610194 \/ 0x610195 <= fst iv)
}.

Lemma locale_imgA : forall k, (k < 6)%nat ->
  rdn ASEGS (fun _ => None) (Z_to_bv 64 (0x630fd0 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros k Hk. do 6 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibInit.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
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
    exists av uid rnd tid canary hw, lib_init_facts (lib_view Lay ar) av uid rnd tid canary hw M.
  Proof.
    intros vals ebs kn LB LK cr A M model p0 HK HB P1 D (uidz & rnd & hwz & AW & AU & AH & AR1 & AR2 & AP & AP8).
    pose proof Hsp as Hsp'. set (E := Env (vals_ev vals) ebs) in *. set (MV := mrestrict (ahid A model) M) in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as (HOFF & _).
    rewrite forallb_forall in HB.
    assert (KB : forall K, In K LIBINIT_KN -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    assert (FULLR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M (Z_to_bv 64 a) n = Some bs)
      by (intros a n bs Hr; exact (rdn_of_mrestrict ASEGS _ M HOFF n _ bs Hr)).
    assert (NONE : forall lo hi, In (KImg lo hi) LIBINIT_KN -> hi <= 0x633000 -> forall i, 0 <= lo -> lo <= i < hi -> M (Z_to_bv 64 i) = None).
    { intros lo hi Hin Hhi i Hlo Hi. pose proof (kimg_clear E MV kn lo hi HK (KB _ Hin) i Hi) as X. unfold MV, mrestrict in X.
      rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ i D ltac:(lia)) in X. exact X. }
    assert (KW : forall a (w : nat) v, In (KWord (SA (ELit 0) a) w v) LIBINIT_KN -> 0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
                 rdn ASEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v))).
    { intros a w v Hin Ha Hw. apply FULLR. exact (kword_lit sp0 E MV kn a w v HK (KB _ Hin) Ha Hw). }
    pose proof (KW 6491464 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CG.
    pose proof (KW 6360128 8%nat (ELit 6360128) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CS.
    pose proof (KW 6360160 4%nat (EVar 4) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CT.
    pose proof (KW 6360312 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CC.
    pose proof (KW 6360280 8%nat (ELit 6492112) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CL.
    pose proof (KW 6492064 8%nat (EAlu ALU_ADD (EVar 1) (ELit (-160))) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CA.
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
    destruct DLC as [d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 dimg _ _].
    unfold lib_init_facts. cbn [lib_view ll_heap heap_view HeapIface.hl_segs hl_sptop ll_init_img ll_td_self ll_td_tid ll_td_locale ll_locale ll_td_canary ll_guard ll_auxvp].
    rewrite LayL, (dla_segs _ _ _ _ DL), (dla_sptop _ _ _ _ DL), d1, d2, d3, d4, d5, d6, d7. unfold cellz.
    rewrite !Z_to_bv_bv_unsigned.
    split. { intros iv a Hiv Ha. destruct (dimg iv Hiv) as (lo & hi & Hin & H1 & H2).
             unfold LIBINIT_IMG in Hin. cbn [In] in Hin.
             destruct Hin as [X|[X|[X|[X|[X|[]]]]]]; injection X as <- <-;
               [apply (NONE 65536 880640) | apply (NONE 6357393 6357396) | apply (NONE 6357397 6360120) | apply (NONE 892736 892792) | apply (NONE 6492112 6492160)];
               first [lia | (unfold LIBINIT_KN; cbn [In]; tauto)]. }
    split; [exact CS|]. split; [exact CT|]. split; [lia|]. split; [exact CL|].
    split. { intros k Hk. apply (img_cell M _ 8%nat _ (locale_imgA k Hk)); [lia | cbn; lia|].
             intros i Hi. apply (NONE 6492112 6492160); [unfold LIBINIT_KN; cbn [In]; tauto | lia | lia | cbn in Hi; lia]. }
    split; [exact CC|]. split; [exact CG|]. split; [pose proof (bv_unsigned_in_range _ (vals_ev vals 3)) as X; change (bv_modulus 64) with (2 ^ 64) in X; lia|].
    split; [exact CA|]. split; [unfold av; lia|]. split; [unfold av; lia|].
    split. { unfold av. rewrite <- Zminus_mod_idemp_l, AP8. reflexivity. }
    split. { intros j Hj. unfold auxv_words. cbn [lib_view ll_phdr ll_phent ll_phnum]. rewrite d8, d9, d10.
             apply (rdn_tr M0 M _ 8%nat _ (AW j Hj)); [unfold av; lia | unfold av; cbn; lia|].
             intros i Hi. apply (di_above _ _ _ _ _ _ _ _ _ _ D). unfold av in *. cbn in Hi. lia. }
    repeat split; lia.
  Qed.
End LibInit.
End FPX_1.
