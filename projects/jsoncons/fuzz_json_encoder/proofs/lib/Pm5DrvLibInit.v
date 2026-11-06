(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefPrintfLib
  HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA LibIface PmLibIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Pm5DrvEntry Pm5Drv_defs Pm5DrvLib Pm5DrvRead Pm5DrvStdio.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Definition LIBINIT_KN : list kentry :=
  [KImg 65536 1466368; KImg 6946321 6952896; KImg 1477728 1477960; KImg 7084888 7084936; KImg 7085056 7085060;
   KWord (SA (ELit 0) 7084240) 8 (EVar 3); KWord (SA (ELit 0) 6952904) 8 (ELit 6952904); KWord (SA (ELit 0) 6952936) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 6953088) 8 (EVar 3); KWord (SA (ELit 0) 6953056) 8 (ELit 7084888); KWord (SA (ELit 0) 7084840) 8 (EAlu ALU_ADD (EVar 1) (ELit (-160)))].
(* [comment removed for export] *)
Definition ATX_KN : list kentry :=
  [KWord (SA (ELit 0) 7084256) 1 (ELit 0); KWord (SA (ELit 0) 7084260) 4 (ELit 0); KWord (SA (ELit 0) 7084272) 8 (ELit 7084280); KWord (SA (ELit 0) 7084264) 4 (ELit 2);
   KWord (SA (ELit 0) 7084280) 8 (ELit 0); KWord (SA (ELit 0) 7084288) 8 (ELit 1332024); KWord (SA (ELit 0) 7084544) 8 (ELit 656352); KWord (SA (ELit 0) 7084296) 8 (ELit 1332024); KWord (SA (ELit 0) 7084552) 8 (ELit 724392); KWord (SA (ELit 0) 7084835) 1 (ELit 0)].
(* [comment removed for export] *)
Definition LIBINIT_IMG : list (Z * Z) := [(65536, 1466368); (6946321, 6952896); (1477728, 1477960); (7084888, 7084936); (7085056, 7085060)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Record drv_lib_cellsA (Lay : lib_layoutA) : Prop := DRV_LIB_CELLSA {
  dlc_td_self : lla_td_self Lay = 0x6a17c8;  dlc_td_tid : lla_td_tid Lay = 0x6a17e8;  dlc_td_canary : lla_td_canary Lay = 0x6a1880;
  dlc_td_locale : lla_td_locale Lay = 0x6a1860;  dlc_locale : lla_locale Lay = 0x6c1b58;  dlc_guard : lla_guard Lay = 0x6c18d0;
  dlc_auxvp : lla_auxvp Lay = 0x6c1b28;  dlc_phdr : lla_phdr Lay = 0x10040;  dlc_phent : lla_phent Lay = 56;  dlc_phnum : lla_phnum Lay = 11;
  dlc_init_img : forall iv, In iv (lla_init_img Lay) -> exists lo hi, In (lo, hi) LIBINIT_IMG /\ lo <= fst iv /\ snd iv <= hi;
  (* [comment removed for export] *)
  dlc_rw_lo : lla_rw_lo Lay <= 0x168e38;
  dlc_initc : forall iv, In iv (lla_initc Lay) -> 0 <= fst iv /\ snd iv <= 0x6c4000 /\ (snd iv <= 0x168e38 \/ 0x168f20 <= fst iv) /\ (snd iv <= 0x6c20b0 \/ 0x6c24b0 <= fst iv);
  (* [comment removed for export] *)
  dlc_init_cells : lla_init_cells Lay = [];
  (* [comment removed for export] *)
  dlc_initc_aef : forall iv, In iv (lla_initc Lay) -> snd iv <= 6946324 \/ 6946324 + 1 <= fst iv
}.

Lemma locale_imgA : forall k, (k < 6)%nat ->
  rdn ASEGS (fun _ => None) (Z_to_bv 64 (0x6c1b58 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
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
    assert (NONE : forall lo hi, In (KImg lo hi) LIBINIT_KN -> hi <= 0x6c4000 -> forall i, 0 <= lo -> lo <= i < hi -> M (Z_to_bv 64 i) = None).
    { intros lo hi Hin Hhi i Hlo Hi. pose proof (kimg_clear E MV kn lo hi HK (KB _ Hin) i Hi) as X. unfold MV, mrestrict in X.
      rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ i D ltac:(lia)) in X. exact X. }
    assert (KW : forall a (w : nat) v, In (KWord (SA (ELit 0) a) w v) LIBINIT_KN -> 0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
                 rdn ASEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v))).
    { intros a w v Hin Ha Hw. apply FULLR. exact (kword_lit sp0 E MV kn a w v HK (KB _ Hin) Ha Hw). }
    pose proof (KW 7084240 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CG.
    pose proof (KW 6952904 8%nat (ELit 6952904) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CS.
    pose proof (KW 6952936 4%nat (EVar 4) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CT.
    pose proof (KW 6953088 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CC.
    pose proof (KW 6953056 8%nat (ELit 7084888) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CL.
    pose proof (KW 7084840 8%nat (EAlu ALU_ADD (EVar 1) (ELit (-160))) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CA.
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
    destruct DLC as [d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 dimg _ _ dic _].
    unfold lib_init_facts. cbn [lib_view ll_heap heap_view HeapIface.hl_segs hl_sptop ll_init_img ll_td_self ll_td_tid ll_td_locale ll_locale ll_td_canary ll_guard ll_auxvp].
    rewrite LayL, (dla_segs _ _ _ _ DL), (dla_sptop _ _ _ _ DL), d1, d2, d3, d4, d5, d6, d7. unfold cellz.
    rewrite !Z_to_bv_bv_unsigned.
    split. { intros iv a Hiv Ha. destruct (dimg iv Hiv) as (lo & hi & Hin & H1 & H2).
             unfold LIBINIT_IMG in Hin. cbn [In] in Hin.
             destruct Hin as [X|[X|[X|[X|[X|[]]]]]]; injection X as <- <-;
               [apply (NONE 65536 1466368) | apply (NONE 6946321 6952896) | apply (NONE 1477728 1477960) | apply (NONE 7084888 7084936) | apply (NONE 7085056 7085060)];
               first [lia | (unfold LIBINIT_KN; cbn [In]; tauto)]. }
    split; [exact CS|]. split; [exact CT|]. split; [lia|]. split; [exact CL|].
    split. { intros k Hk. apply (img_cell M _ 8%nat _ (locale_imgA k Hk)); [lia | cbn; lia|].
             intros i Hi. apply (NONE 7084888 7084936); [unfold LIBINIT_KN; cbn [In]; tauto | lia | lia | cbn in Hi; lia]. }
    split; [exact CC|]. split; [exact CG|]. split; [pose proof (bv_unsigned_in_range _ (vals_ev vals 3)) as X; change (bv_modulus 64) with (2 ^ 64) in X; lia|].
    split; [exact CA|]. split; [unfold av; lia|]. split; [unfold av; lia|].
    split. { unfold av. rewrite <- Zminus_mod_idemp_l, AP8. reflexivity. }
    split. { intros j Hj. unfold auxv_words. cbn [lib_view ll_phdr ll_phent ll_phnum]. rewrite d8, d9, d10.
             apply (rdn_tr M0 M _ 8%nat _ (AW j Hj)); [unfold av; lia | unfold av; cbn; lia|].
             intros i Hi. apply (di_above _ _ _ _ _ _ _ _ _ _ D). unfold av in *. cbn in Hi. lia. }
    repeat split; try lia.
    all: match goal with |- forall c, In c _ -> _ => intros c Hc; cbn [ll_init_cells lib_view] in Hc; rewrite dic in Hc; destruct Hc | _ => idtac end.      (* [comment removed for export] *)
    all: fail "R23 DrvLibInit: unexpected remaining goal".
  Qed.
  Theorem atexit_init_at_call : forall vals ebs kn LB LK cr A M (model : Model),
    know_ok ASEGS (Env (vals_ev vals) ebs) (mrestrict (ahid A model) M) kn ->
    forallb (fun K => existsb (kentry_eqb K) kn) ATX_KN = true ->
    dinvA LB LK cr A M model ->
    lla_atexit Lay = 7084256 -> lla_hs0 Lay = [(1332024, 656352); (1332024, 724392)] ->      (* [comment removed for export] *) lla_need_locks Lay = 7084835 ->
    atexit_state_at (hl_segs (lla_L Lay)) (lla_atexit Lay) M (lla_hs0 Lay) /\ cell_is (hl_segs (lla_L Lay)) M (lla_need_locks Lay) 1 0.
  Proof.
    intros vals ebs kn LB LK cr A M model HK HB D EA EH EN. rewrite LayL, (dla_segs _ _ _ _ DL), EA, EH, EN.
    pose proof Hsp as Hsp'. set (E := Env (vals_ev vals) ebs) in *. set (MV := mrestrict (ahid A model) M) in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as (HOFF & _).
    rewrite forallb_forall in HB.
    assert (KB : forall K, In K ATX_KN -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    assert (FULLR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M (Z_to_bv 64 a) n = Some bs)
      by (intros a n bs Hr; exact (rdn_of_mrestrict ASEGS _ M HOFF n _ bs Hr)).
    assert (KW : forall a (w : nat) v, In (KWord (SA (ELit 0) a) w (ELit v)) ATX_KN -> (0 <=? a) && (a + Z.of_nat w <=? 2 ^ 63) = true -> cell_is ASEGS M a w v).
    { intros a w v Hin Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. unfold cell_is. apply FULLR. exact (kword_lit sp0 E MV kn a w (ELit v) HK (KB _ Hin) B1 B2). }
    assert (IN : forall K, existsb (kentry_eqb K) ATX_KN = true -> In K ATX_KN).
    { intros K Hb. apply existsb_exists in Hb as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact Hin. }
    split; [|(apply KW; [apply IN; vm_compute; reflexivity | reflexivity])].
    unfold atexit_state_at. split; [(apply KW; [apply IN; vm_compute; reflexivity | reflexivity])|]. split; [(apply KW; [apply IN; vm_compute; reflexivity | reflexivity])|].
    split; [cbn; lia|]. split; [(apply KW; [apply IN; vm_compute; reflexivity | reflexivity])|]. split; [(apply KW; [apply IN; vm_compute; reflexivity | reflexivity])|]. split; [(apply KW; [apply IN; vm_compute; reflexivity | reflexivity])|].
    intros i f a Hn. destruct i as [|[|i]]; [injection Hn as <- <-; split; (apply KW; [apply IN; vm_compute; reflexivity | reflexivity])
      | injection Hn as <- <-; split; (apply KW; [apply IN; vm_compute; reflexivity | reflexivity]) | destruct i; discriminate Hn].
  Qed.
End LibInit.
End FPX_1.
