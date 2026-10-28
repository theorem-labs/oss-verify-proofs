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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b Ba0DrvExit_b
  Ba0DrvA_b Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvC_defs_b Ba0DrvC_b Ba0DrvE_defs_b Ba0DrvE_b Ba0DrvExitM_b Ba0DiagFwrite_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition IMG_FW_A : list (Z * Z) :=
  [(0x10000, 0x139000); (0x13bbe0, 0x13bcc8); (0x13bdb8, 0x13c580); (0x662290, 0x673ca8); (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x6951b8); (0x6951c0, 0x696000)].
Definition keep_fwA (so : Z) (kn : list kentry) : list kentry := kn_keep 0 so 2320 [] [] [] IMG_FW_A IMG_RW_A kn.
(* [comment removed for export] *)
Definition XKNM : list kentry :=
  map (fun c : Z * nat * Z => KWord (SA (ELit 0) (fst (fst c))) (snd (fst c)) (ELit (snd c))) XC9_CELLS
  ++ [KWord (SA (ELit 0) 6765656) 4 (EVar 4); KRange (EVar 4) 1 4194303; KImg 0x13bea0 0x13c580; KImg 1293752 1293984; KImg 65536 1282048].
(* [comment removed for export] *)
Definition stderrM6 (MV : word -> option byte) : Prop :=
  stderrMA MV /\ rdn ASEGS MV (Z_to_bv 64 1293744) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1293512)) /\ rdn ASEGS MV (Z_to_bv 64 1293652) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295)).
Lemma stderrM6_tr : forall (MV MV' : word -> option byte), stderrM6 MV -> (forall a, 1293512 <= a < 1293752 -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) -> stderrM6 MV'.
Proof.
  intros MV MV' ((S1 & S2 & S3 & S4) & S5 & S6) AG.
  assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 1293512 <= a -> a + Z.of_nat n <= 1293752 -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Hr H1 H2. apply (rdn_tr MV MV' a n bs Hr); [lia | lia|]. intros i Hi. apply AG. lia. }
  unfold stderrM6, stderrMA. repeat split; apply TR; first [assumption | cbn; lia].
Qed.
Lemma msg_short_img : rdn ASEGS (fun _ => None) (Z_to_bv 64 137179) 31 = Some msg_short.
Proof. vm_compute. apply f_equal. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma msg_overrun_img : rdn ASEGS (fun _ => None) (Z_to_bv 64 90411) 31 = Some msg_overrun.
Proof. vm_compute. apply f_equal. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma fds0_lookup2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. vm_compute. reflexivity. Qed.

Section FwKeep.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  #[using="Hsp"] Lemma regions_fwA : forall vals ebs so,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> - 2 ^ 22 <= so <= 0 ->
    regions_ok ASEGS 0 so 2320 [] [] [] IMG_FW_A IMG_RW_A E (fun a => ~ Wfw (bv_unsigned sp0 + so) a) (fun a => bv_unsigned sp0 + so - 2320 <= a < bv_unsigned sp0 + so).
  Proof.
    intros vals ebs so E P0 Hso. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold Wfw. lia.
    - intros z Hz. right. lia.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_FW_A in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]; split; [lia|]; intros a Ha; unfold Wfw; lia)|]). destruct Hin.
    - intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
      intros Mx d m Hd Hm.
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x662290) (Z_to_bv 64 d) 65536%nat m 0x662290 0x672290);
        first [exact (wseg_stage) | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.
End FwKeep.

(* [comment removed for export] *)
Section FPX_0. Context {fx : PropExec.FPState}.
Definition rMS := Eval vm_compute in runA scr0 (SS 0x12a8dc srGLA [] (knGA 0 5) 71).
Definition srMS : list expr := Eval vm_compute in s_regs (fst (fst rMS)).
Definition knMS : list kentry := Eval vm_compute in kn_after rMS (knGA 0 5).
Definition srMS1 : list expr := Eval vm_compute in sr_after_call_j srMS (map ridx c_kept) 71.
Definition knMS1 : list kentry := Eval vm_compute in keep_fwA MSO knMS.
Definition rMS2 := Eval vm_compute in runA scr0 (SS 0xa7cf8 srMS1 [] knMS1 103).
Definition srMS2 : list expr := Eval vm_compute in s_regs (fst (fst rMS2)).
Definition knMS2 : list kentry := Eval vm_compute in kn_after rMS2 knMS1.
Definition srMS3 : list expr := Eval vm_compute in sr_after_call_j srMS2 (map ridx c_kept) 103.
Definition knMS3 : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knMS2.
Definition rMS4 := Eval vm_compute in runA scr0 (SS 0xa7d00 srMS3 [] knMS3 135).
Definition srMS4 : list expr := Eval vm_compute in s_regs (fst (fst rMS4)).
Definition knMS4 : list kentry := Eval vm_compute in kn_after rMS4 knMS3.
Definition rMO := Eval vm_compute in runA (SCR [true] [] []) (SS 0x12a8dc srGLA [] knGLA 73).
Definition srMO : list expr := Eval vm_compute in s_regs (fst (fst rMO)).
Definition knMO : list kentry := Eval vm_compute in kn_after rMO knGLA.
Definition srMO1 : list expr := Eval vm_compute in sr_after_call_j srMO (map ridx c_kept) 73.
Definition knMO1 : list kentry := Eval vm_compute in keep_fwA MSO knMO.
Definition rMO2 := Eval vm_compute in runA scr0 (SS 0xa7cf8 srMO1 [] knMO1 105).
Definition srMO2 : list expr := Eval vm_compute in s_regs (fst (fst rMO2)).
Definition knMO2 : list kentry := Eval vm_compute in kn_after rMO2 knMO1.
Definition srMO3 : list expr := Eval vm_compute in sr_after_call_j srMO2 (map ridx c_kept) 105.
Definition knMO3 : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knMO2.
Definition rMO4 := Eval vm_compute in runA scr0 (SS 0xa7d00 srMO3 [] knMO3 137).
Definition srMO4 : list expr := Eval vm_compute in s_regs (fst (fst rMO4)).
Definition knMO4 : list kentry := Eval vm_compute in kn_after rMO4 knMO3.

End FPX_0.
Lemma msg_itinerary_okA :
  (s_pc (fst (fst rMS)), s_log (fst (fst rMS)), s_pc (fst (fst rMS2)), snd (fst rMS2), s_log (fst (fst rMS2)), s_pc (fst (fst rMS4)), snd (fst rMS4), s_log (fst (fst rMS4)))
  = (0x63394, [], 0x79814, [], [], 0x118878, [], [])
  /\ (nth 1 srMS (ELit 0), nth 2 srMS (ELit 0), nth 10 srMS (ELit 0), nth 11 srMS (ELit 0), nth 12 srMS (ELit 0), nth 13 srMS (ELit 0))
     = (ELit 687352, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 137179, ELit 31, ELit 1, ELit 1293512)
  /\ (nth 1 srMS2 (ELit 0), nth 2 srMS2 (ELit 0), nth 4 srMS2 (ELit 0), nth 10 srMS2 (ELit 0)) = (ELit 0xa7d00, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6765824, EVar 48)
  /\ (nth 2 srMS4 (ELit 0), nth 4 srMS4 (ELit 0), nth 10 srMS4 (ELit 0)) = (EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 6765824, ELit 2)
  /\ forallb (fun K => existsb (kentry_eqb K) knMS4) XKNM = true /\ has_window knMS4 = true
  /\   (s_pc (fst (fst rMO)), s_log (fst (fst rMO)), s_pc (fst (fst rMO2)), snd (fst rMO2), s_log (fst (fst rMO2)), s_pc (fst (fst rMO4)), snd (fst rMO4), s_log (fst (fst rMO4)))
  = (0x63394, [], 0x79814, [], [], 0x118878, [], [])
  /\ (nth 1 srMO (ELit 0), nth 2 srMO (ELit 0), nth 10 srMO (ELit 0), nth 11 srMO (ELit 0), nth 12 srMO (ELit 0), nth 13 srMO (ELit 0))
     = (ELit 687352, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 90411, ELit 31, ELit 1, ELit 1293512)
  /\ (nth 1 srMO2 (ELit 0), nth 2 srMO2 (ELit 0), nth 4 srMO2 (ELit 0), nth 10 srMO2 (ELit 0)) = (ELit 0xa7d00, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6765824, EVar 48)
  /\ (nth 2 srMO4 (ELit 0), nth 4 srMO4 (ELit 0), nth 10 srMO4 (ELit 0)) = (EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 6765824, ELit 2)
  /\ forallb (fun K => existsb (kentry_eqb K) knMO4) XKNM = true /\ has_window knMO4 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Arm.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Hypothesis Hdgm : incl DGM_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables p0 p1 can : word.
  Variable LK0 : list fframe.
  Variable A0 : list (Z * Z).
  Variable CAP : Z.
  Hypothesis HCAP : 65536 <= CAP <= 67108864.
  Variable crC : credit.
  Hypothesis HLEN : Z.of_nat (length fdata) < CAP.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation ENVG := (ENVA fdata).
  #[local] Notation rom := (seg_rom ASEGS).
  #[local] Notation KX := (t_exit (exit_code 2) fs0).

  (* [comment removed for export] *)
  #[using="sp0 Hsp CAP HCAP"] Lemma exitm_of_kn : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKNM = true -> stderrM6 MV ->
    exitMA (bv_unsigned (vals_ev vals 4)) MV /\ stdoutPA MV /\ (forall i, 65536 <= i < 1282048 -> MV (Z_to_bv 64 i) = None).
  Proof.
    intros vals MV kn HK HB ((S1 & S2 & S3 & S4) & S5 & S6). rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKNM -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bea0 0x13c580 HK (KB (KImg 0x13bea0 0x13c580) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    pose proof (kimg_clear (ENVG vals) MV kn 1293752 1293984 HK (KB (KImg 1293752 1293984) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLo.
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bea0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    assert (ICo : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (1293752 <=? a) && (a + Z.of_nat n <=? 1293984) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLo. lia. }
    assert (KW : forall a (w : nat) v, In (KWord (SA (ELit 0) a) w v) XKNM -> (0 <=? a) && (a + Z.of_nat w <=? 2 ^ 63) = true -> rdn ASEGS MV (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot (ENVG vals) v))).
    { intros a w v Hin Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (kword_lit sp0 _ MV kn a w v HK (KB _ Hin) B1 B2). }
    split; [|split].
    - unfold exitMA. split; [|split; [|split]].
      + unfold cells_at, XCM_CELLS.
        constructor; [exact (KW 6897520 4%nat (ELit 0) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6897555 1%nat (ELit 0) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6896992 8%nat (ELit 6897000) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6896984 4%nat (ELit 1) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6897008 8%nat (ELit 1148964) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6897264 8%nat (ELit 619876) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6896980 4%nat (ELit 0) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6897000 8%nat (ELit 0) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (KW 6898952 8%nat (ELit 0) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl)|].
        constructor; [exact (ICb 1294224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293992)) ltac:(img_rd) eq_refl)|].
        constructor; [exact (ICb 1294132 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
        constructor; [exact (ICb 1294032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
        constructor; [exact (ICb 1294048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
        constructor; [exact (ICb 1294000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
        constructor; [exact (ICb 1294008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
        constructor; [exact (ICb 1293984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293752)) ltac:(img_rd) eq_refl)|].
        constructor; [exact S5|]. constructor; [exact S6|]. constructor; [exact S1|]. constructor; [exact S2|]. constructor; [exact S3|]. constructor; [exact S4|].
        constructor.
      + rewrite Z_to_bv_bv_unsigned. exact (KW 6765656 4%nat (EVar 4) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto) eq_refl).
      + pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
        apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
        pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
      + intros i Hi. apply CLb. lia.
    - unfold stdoutPA.
      split; [exact (ICo 1293892 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|]. split; [exact (ICo 1293792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      split; [exact (ICo 1293808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|]. split; [exact (ICo 1293760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      exact (ICo 1293768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl).
    - exact (kimg_clear (ENVG vals) MV kn 65536 1282048 HK (KB (KImg 65536 1282048) ltac:(unfold XKNM; cbn [In map XC9_CELLS app fst snd]; tauto))).
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok Hsp DL fdata CAP HCAP"] Lemma stderr6_call : forall LB LK cr A M (model : Model) LB' LK' cr' A' M' (model' : Model),
    dinvA LB LK cr A M model -> dinvA LB' LK' cr' A' M' model' ->
    (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    stderrM6 (mrestrict (ahid A model) M) -> stderrM6 (mrestrict (ahid A' model') M').
  Proof.
    intros LB LK cr A M model LB' LK' cr' A' M' model' D D' FR SE.
    apply (stderrM6_tr _ _ SE). intros a Ha. unfold mrestrict.
    rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ a D) by lia.
    rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ a D') by lia.
    apply (FR 0x13bbe0 0x13c580); [unfold IMG_CLIENT_A; cbn [In]; tauto | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma knMS1_eq : keep_fwA MSO knMS = knMS1.  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma srMS3_eq : sr_after_call_j srMS2 (map ridx c_kept) 103 = srMS3.  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma knMS3_eq : keep_allocA MSO 4096 [] [] knMS2 = knMS3.  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex CAP HCAP"] Lemma exit_MS : forall (fxq : PropExec.FPState) vals R M (model : Model) A,
    length vals = 135%nat -> hdr_valsA sp0 p0 p1 can vals ->
    regs_ok (ENVG vals) srMS3 R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knMS3 ->
    dinvA [] LK0 crC A M model -> m_fs model = fs0 ->
    stderrM6 (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0xa7d00) M rom) model) KX.
  Proof.
    intros fxq vals R M model A HL HV HR HK DI F2 SE.
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 135%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (_ & Q2). rewrite F2 in Q2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SE.
    set (MV := mrestrict (ahid A model0) M) in *.
    set (S := usp - 48).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HS16 : S mod 16 = 0) by (unfold S; clear - Hal; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (exitm_of_kn vals MV _ HK0 ltac:(vm_compute; reflexivity) SE) as (XM & SOP & IMGc).
    assert (XP : exit_preM ar HI sp0 M0 [] LK0 crC A M model0 S (bv_unsigned (vals_ev vals 4))).
    { unfold exit_preM. split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
      split; [exact HS16|].
      split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
      split; [exact IMGc | exact XM]. }
    assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
    { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
    assert (G4r : getr R0 4%bv = Z_to_bv 64 6765824) by (regv HR0 (4%bv : reg); reflexivity).
    assert (G10r : getr R0 10%bv = Z_to_bv 64 2) by (regv HR0 (10%bv : reg); reflexivity).
    unfold exit_code. rewrite <- Q2.
    exact (exit_run_m scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK0 crC A M model0 R0 S 2 _ XP ltac:(lia) G2r G4r G10r SOP).
  Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex M0_def HCAP"] Lemma tail_MS : forall (fxq : PropExec.FPState) vals R M (model : Model) A (A1 : Z),
    length vals = 103%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 ->
    regs_ok (ENVG vals) srMS1 R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knMS1 ->
    dinvA [(A1, CAP)] LK0 crC A M model -> m_fs model = fs0 ->
    stderrM6 (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0xa7cf8) M rom) model) KX.
  Proof.
    intros fxq vals R M model A A1 HL HV P48 HR HK DI F2 SE.
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 103%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (_ & Q2). rewrite F2 in Q2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SE.
    apply (@afree_site fxq scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ _ _ R0 M model0 [(A1, CAP)] LK0 crC A A1 CAP MSO [] [] 0xa7d00 KX HR0 HK0).
    - rewrite HL. vm_compute. reflexivity.
    - rewrite HL. vm_compute. reflexivity.
    - rewrite HL. lia.
    - exact P0.
    - vm_compute. reflexivity.
    - regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. apply alu_add_w_litA.
    - unfold MSO. lia.
    - reflexivity.
    - left. reflexivity.
    - regv HR0 (10%bv : reg). cbn [edenot ev ENVA]. exact P48.
    - regv HR0 (4%bv : reg). reflexivity.
    - regv HR0 (1%bv : reg). reflexivity.
    - lia.
    - reflexivity.
    - exact DI0.
    - intros i nb Hf. discriminate Hf.
    - intros v b Hf. discriminate Hf.
    - apply t_exit_has_nil.
    - intros R' M' model' A' vals' E' HL' HR' HK' DI' MRT HINC' _ _ FRc.
      rewrite lb_remove_hdA in DI'. rewrite HL in HL', HR'.
      destruct (model_rt_fds _ _ MRT) as (_ & Q2'). rewrite Q2 in Q2'.
      pose proof (stderr6_call _ _ _ _ _ _ _ _ _ _ _ _ DI0 DI' FRc SE) as SE'.
      apply (exit_MS fxq vals' R' M' model' A' HL').
      + subst vals'. unfold hdr_valsA in *. rewrite !vals_ev_app_l by (rewrite HL; lia). exact HV.
      + rewrite <- srMS3_eq. exact HR'.
      + rewrite <- knMS3_eq. exact HK'.
      + exact DI'.
      + exact Q2'.
      + exact SE'.
  Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdgm M0_def HCAP"] Lemma site_MS : forall (fxq : PropExec.FPState) vals R M (model : Model) A (A1 : Z),
    length vals = 71%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 ->
    regs_ok (ENVG vals) srMS R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knMS ->
    dinvA [(A1, CAP)] LK0 crC A M model -> m_fds model = fds0 -> m_fs model = fs0 ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x63394) M rom) model) (t_die msg_short fs0).
  Proof.
    intros fxq vals R M model A A1 HL HV P48 HR HK DI F1 F2.
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    set (S := usp - 128). set (MV := mrestrict (ahid A model) M) in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HS16 : S mod 16 = 0) by (unfold S; clear - Hal; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (HW : has_window knMS = true) by (vm_compute; reflexivity).
    assert (G1r : getr R 1%bv = Z_to_bv 64 687352) by (regv HR (1%bv : reg); reflexivity).
    assert (G2r : getr R 2%bv = Z_to_bv 64 S) by (regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA).
    assert (G10r : getr R 10%bv = Z_to_bv 64 137179) by (regv HR (10%bv : reg); reflexivity).
    assert (G11r : getr R 11%bv = Z_to_bv 64 31) by (regv HR (11%bv : reg); reflexivity).
    assert (G12r : getr R 12%bv = Z_to_bv 64 1) by (regv HR (12%bv : reg); reflexivity).
    assert (G13r : getr R 13%bv = Z_to_bv 64 1293512) by (regv HR (13%bv : reg); reflexivity).
    assert (CANc : rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
    { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 6896960 8%nat (EVar 3) HK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
    pose proof (kimg_clear _ MV _ 1293512 1293752 HK ltac:(vm_compute; reflexivity)) as SEIMG.
    assert (WIN : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
      by (intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK HW P0 Ha Hn d k Hd Hk)).
    unfold t_die.
    apply (@fwrite1_run fxq scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hdgm M0 [(A1, CAP)] LK0 crC A M model R S (bv_unsigned can) msg_short KX DI
             ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 (u64_range can) G1r G2r G10r G11r G12r G13r WIN
             (kimg_clear _ MV _ 65536 1282048 HK ltac:(vm_compute; reflexivity)) SEIMG CANc msg_short_img).
    - rewrite F1. exact fds0_lookup2.
    - apply t_exit_has_nil.
    - intros fx' R' M1 model1 D1 SBM1 KEPT SEM FRM FRV GROW.
      set (vals' := vals ++ junk_vals R').
      assert (HL' : length vals' = 103%nat) by (unfold vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (unfold vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      apply (tail_MS fx' vals' R' M1 model1 A A1 HL').
      + unfold vals', hdr_valsA in *. rewrite !vals_ev_app_l by (rewrite HL; lia). exact HV.
      + unfold vals'. rewrite vals_ev_app_l by (rewrite HL; lia). exact P48.
      + pose proof (regs_after_keeps vals _ srMS R R' c_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEPT (c_kept_no0A)) as X. rewrite HL in X. exact X.
      + pose proof (env_app_know ASEGS vals (junk_vals R') _ _ knMS ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1. fold vals' in HK1.
        rewrite <- knMS1_eq. unfold keep_fwA.
        refine (know_keep_sound ASEGS 0 MSO 2320 [] [] [] IMG_FW_A IMG_RW_A (ENVG vals')
                  (fun a => ~ Wfw (usp + MSO) a) (fun a => usp + MSO - 2320 <= a < usp + MSO) _
                  (mrestrict (ahid A model) M) (mrestrict (ahid A model1) M1) _ _ knMS HK1).
        * apply (regions_fwA sp0 Hsp vals' _ MSO); [exact P0' | unfold MSO; lia].
        * intros a Ha Hn. exact (FRV a Ha Hn).
        * intros a Ha. apply GROW. apply (store_ok_defined sp0); [unfold MSO in Ha; lia|].
          pose proof (WIN a 1 ltac:(unfold MSO in Ha; lia) ltac:(unfold MSO in Ha; lia) 0 1%nat ltac:(lia) ltac:(lia)) as W.
          rewrite Z.add_0_r in W. exact W.
      + exact D1.
      + rewrite <- F2. exact (proj2 (sbm_fds model model1 SBM1)).
      + assert (ICe : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (1293652 <=? a) && (a + Z.of_nat n <=? 1293752) = true ->
                  rdn ASEGS (mrestrict (ahid A model1) M1) (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2.
          apply (rdn_tr MV _ a n bs); [apply (img_cell MV a n bs Hr); [lia | lia | intros i Hi; apply SEIMG; lia] | lia | lia|].
          intros i Hi. apply FRV; [lia|]. unfold Wfw, S. clear - Hsp' B1 B2 Hi. lia. }
        split; [exact SEM|].
        split; [exact (ICe 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl) | exact (ICe 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma knMO1_eq : keep_fwA MSO knMO = knMO1.  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma srMO3_eq : sr_after_call_j srMO2 (map ridx c_kept) 105 = srMO3.  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma knMO3_eq : keep_allocA MSO 4096 [] [] knMO2 = knMO3.  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex CAP HCAP"] Lemma exit_MO : forall (fxq : PropExec.FPState) vals R M (model : Model) A,
    length vals = 137%nat -> hdr_valsA sp0 p0 p1 can vals ->
    regs_ok (ENVG vals) srMO3 R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knMO3 ->
    dinvA [] LK0 crC A M model -> m_fs model = fs0 ->
    stderrM6 (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0xa7d00) M rom) model) KX.
  Proof.
    intros fxq vals R M model A HL HV HR HK DI F2 SE.
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 137%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (_ & Q2). rewrite F2 in Q2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SE.
    set (MV := mrestrict (ahid A model0) M) in *.
    set (S := usp - 48).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HS16 : S mod 16 = 0) by (unfold S; clear - Hal; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (exitm_of_kn vals MV _ HK0 ltac:(vm_compute; reflexivity) SE) as (XM & SOP & IMGc).
    assert (XP : exit_preM ar HI sp0 M0 [] LK0 crC A M model0 S (bv_unsigned (vals_ev vals 4))).
    { unfold exit_preM. split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
      split; [exact HS16|].
      split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
      split; [exact IMGc | exact XM]. }
    assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
    { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
    assert (G4r : getr R0 4%bv = Z_to_bv 64 6765824) by (regv HR0 (4%bv : reg); reflexivity).
    assert (G10r : getr R0 10%bv = Z_to_bv 64 2) by (regv HR0 (10%bv : reg); reflexivity).
    unfold exit_code. rewrite <- Q2.
    exact (exit_run_m scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK0 crC A M model0 R0 S 2 _ XP ltac:(lia) G2r G4r G10r SOP).
  Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex M0_def HCAP"] Lemma tail_MO : forall (fxq : PropExec.FPState) vals R M (model : Model) A (A1 : Z),
    length vals = 105%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 ->
    regs_ok (ENVG vals) srMO1 R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knMO1 ->
    dinvA [(A1, CAP)] LK0 crC A M model -> m_fs model = fs0 ->
    stderrM6 (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0xa7cf8) M rom) model) KX.
  Proof.
    intros fxq vals R M model A A1 HL HV P48 HR HK DI F2 SE.
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 105%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (_ & Q2). rewrite F2 in Q2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SE.
    apply (@afree_site fxq scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ _ _ R0 M model0 [(A1, CAP)] LK0 crC A A1 CAP MSO [] [] 0xa7d00 KX HR0 HK0).
    - rewrite HL. vm_compute. reflexivity.
    - rewrite HL. vm_compute. reflexivity.
    - rewrite HL. lia.
    - exact P0.
    - vm_compute. reflexivity.
    - regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. apply alu_add_w_litA.
    - unfold MSO. lia.
    - reflexivity.
    - left. reflexivity.
    - regv HR0 (10%bv : reg). cbn [edenot ev ENVA]. exact P48.
    - regv HR0 (4%bv : reg). reflexivity.
    - regv HR0 (1%bv : reg). reflexivity.
    - lia.
    - reflexivity.
    - exact DI0.
    - intros i nb Hf. discriminate Hf.
    - intros v b Hf. discriminate Hf.
    - apply t_exit_has_nil.
    - intros R' M' model' A' vals' E' HL' HR' HK' DI' MRT HINC' _ _ FRc.
      rewrite lb_remove_hdA in DI'. rewrite HL in HL', HR'.
      destruct (model_rt_fds _ _ MRT) as (_ & Q2'). rewrite Q2 in Q2'.
      pose proof (stderr6_call _ _ _ _ _ _ _ _ _ _ _ _ DI0 DI' FRc SE) as SE'.
      apply (exit_MO fxq vals' R' M' model' A' HL').
      + subst vals'. unfold hdr_valsA in *. rewrite !vals_ev_app_l by (rewrite HL; lia). exact HV.
      + rewrite <- srMO3_eq. exact HR'.
      + rewrite <- knMO3_eq. exact HK'.
      + exact DI'.
      + exact Q2'.
      + exact SE'.
  Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdgm M0_def HCAP"] Lemma site_MO : forall (fxq : PropExec.FPState) vals R M (model : Model) A (A1 : Z),
    length vals = 73%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 ->
    regs_ok (ENVG vals) srMO R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knMO ->
    dinvA [(A1, CAP)] LK0 crC A M model -> m_fds model = fds0 -> m_fs model = fs0 ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x63394) M rom) model) (t_die msg_overrun fs0).
  Proof.
    intros fxq vals R M model A A1 HL HV P48 HR HK DI F1 F2.
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    set (S := usp - 128). set (MV := mrestrict (ahid A model) M) in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HS16 : S mod 16 = 0) by (unfold S; clear - Hal; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (HW : has_window knMO = true) by (vm_compute; reflexivity).
    assert (G1r : getr R 1%bv = Z_to_bv 64 687352) by (regv HR (1%bv : reg); reflexivity).
    assert (G2r : getr R 2%bv = Z_to_bv 64 S) by (regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA).
    assert (G10r : getr R 10%bv = Z_to_bv 64 90411) by (regv HR (10%bv : reg); reflexivity).
    assert (G11r : getr R 11%bv = Z_to_bv 64 31) by (regv HR (11%bv : reg); reflexivity).
    assert (G12r : getr R 12%bv = Z_to_bv 64 1) by (regv HR (12%bv : reg); reflexivity).
    assert (G13r : getr R 13%bv = Z_to_bv 64 1293512) by (regv HR (13%bv : reg); reflexivity).
    assert (CANc : rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
    { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 6896960 8%nat (EVar 3) HK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
    pose proof (kimg_clear _ MV _ 1293512 1293752 HK ltac:(vm_compute; reflexivity)) as SEIMG.
    assert (WIN : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
      by (intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK HW P0 Ha Hn d k Hd Hk)).
    unfold t_die.
    apply (@fwrite2_run fxq scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hdgm M0 [(A1, CAP)] LK0 crC A M model R S (bv_unsigned can) msg_overrun KX DI
             ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 (u64_range can) G1r G2r G10r G11r G12r G13r WIN
             (kimg_clear _ MV _ 65536 1282048 HK ltac:(vm_compute; reflexivity)) SEIMG CANc msg_overrun_img).
    - rewrite F1. exact fds0_lookup2.
    - apply t_exit_has_nil.
    - intros fx' R' M1 model1 D1 SBM1 KEPT SEM FRM FRV GROW.
      set (vals' := vals ++ junk_vals R').
      assert (HL' : length vals' = 105%nat) by (unfold vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (unfold vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      apply (tail_MO fx' vals' R' M1 model1 A A1 HL').
      + unfold vals', hdr_valsA in *. rewrite !vals_ev_app_l by (rewrite HL; lia). exact HV.
      + unfold vals'. rewrite vals_ev_app_l by (rewrite HL; lia). exact P48.
      + pose proof (regs_after_keeps vals _ srMO R R' c_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEPT (c_kept_no0A)) as X. rewrite HL in X. exact X.
      + pose proof (env_app_know ASEGS vals (junk_vals R') _ _ knMO ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1. fold vals' in HK1.
        rewrite <- knMO1_eq. unfold keep_fwA.
        refine (know_keep_sound ASEGS 0 MSO 2320 [] [] [] IMG_FW_A IMG_RW_A (ENVG vals')
                  (fun a => ~ Wfw (usp + MSO) a) (fun a => usp + MSO - 2320 <= a < usp + MSO) _
                  (mrestrict (ahid A model) M) (mrestrict (ahid A model1) M1) _ _ knMO HK1).
        * apply (regions_fwA sp0 Hsp vals' _ MSO); [exact P0' | unfold MSO; lia].
        * intros a Ha Hn. exact (FRV a Ha Hn).
        * intros a Ha. apply GROW. apply (store_ok_defined sp0); [unfold MSO in Ha; lia|].
          pose proof (WIN a 1 ltac:(unfold MSO in Ha; lia) ltac:(unfold MSO in Ha; lia) 0 1%nat ltac:(lia) ltac:(lia)) as W.
          rewrite Z.add_0_r in W. exact W.
      + exact D1.
      + rewrite <- F2. exact (proj2 (sbm_fds model model1 SBM1)).
      + assert (ICe : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (1293652 <=? a) && (a + Z.of_nat n <=? 1293752) = true ->
                  rdn ASEGS (mrestrict (ahid A model1) M1) (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2.
          apply (rdn_tr MV _ a n bs); [apply (img_cell MV a n bs Hr); [lia | lia | intros i Hi; apply SEIMG; lia] | lia | lia|].
          intros i Hi. apply FRV; [lia|]. unfold Wfw, S. clear - Hsp' B1 B2 Hi. lia. }
        split; [exact SEM|].
        split; [exact (ICe 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl) | exact (ICe 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdgm M0_def HCAP"] Theorem short_armA : (length fdata < 6)%nat -> close_kgA scfg ar HI sp0 fs0 fdata p0 p1 can M0 LK0 A0 CAP crC (t_die msg_short fs0).
  Proof.
    intros Hs. unfold close_kgA. intros vals R M model A A1 HL HV P48 P70 HR HK HC DI HINC G1 G2.
    pose proof HV as (P0 & _). pose proof Hsp as Hsp'.
    specialize (HK 0 5 ltac:(lia)).
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 71%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
    exact (site_MS fx vals R0 M model0 A A1 HL HV P48 HR0 HK0 DI0 F1 F2).
  Qed.

  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdgm M0_def HCAP HLEN"] Theorem overrun_armA : (6 <= length fdata)%nat -> Z.of_nat (length fdata) < 6 + CFGA fdata ->
    close_kgA scfg ar HI sp0 fs0 fdata p0 p1 can M0 LK0 A0 CAP crC (t_die msg_overrun fs0).
  Proof.
    intros Hge Hov. unfold close_kgA. intros vals R M model A A1 HL HV P48 P70 HR HK HC DI HINC G1 G2.
    pose proof Hsp as Hsp'.
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ).
    specialize (HK 6 67108863 ltac:(lia)).
    (* [comment removed for export] *)
    set (vals1 := vals ++ [Z_to_bv 64 (B0A fdata); Z_to_bv 64 (B1A fdata)]).
    assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
    assert (YV : hdr_valsA sp0 p0 p1 can vals1) by (subst vals1; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
    pose proof YV as (Y0 & _).
    assert (Y48 : vals_ev vals1 48 = Z_to_bv 64 A1) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
    assert (Y70 : vals_ev vals1 70 = Z_to_bv 64 (Z.of_nat (length fdata))) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Y71 : vals_ev vals1 71 = Z_to_bv 64 (B0A fdata)).
    { subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    assert (Y72 : vals_ev vals1 72 = Z_to_bv 64 (B1A fdata)).
    { subst vals1. replace 72%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    pose proof (env_app_regs vals [Z_to_bv 64 (B0A fdata); Z_to_bv 64 (B1A fdata)] _ srGLA R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals [Z_to_bv 64 (B0A fdata); Z_to_bv 64 (B1A fdata)] _ _ (knGA 6 67108863) ltac:(rewrite HL; vm_compute; reflexivity) HK) as HKa.
    fold vals1 in HR1, HKa. change (Env (vals_ev vals1) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals1) in HR1, HKa.
    pose proof (content_visA scfg L ar C IL HI HIok sp0 Hsp DL fdata M0 _ _ _ _ _ _ _ (length fdata) fdata DI ltac:(lia) HC) as HCV.
    pose proof (know_GLA sp0 Hsp fdata CAP HCAP HLEN vals1 _ A1 HL1 Y48 HZ HCV Hge Y71 Y72 HKa) as HK1.
    drv_block0 HIok Hsp DL HR1 HK1 DI Y0 (SCR [true] [] []) 73%nat.
    { apply (ltu_hdr_scA sp0 Hsp fdata CAP HCAP HLEN vals1 _ true Y70 Y71 Y72). apply Z.ltb_lt. lia. }
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
    exact (site_MO fx vals1 R0 M model0 A A1 HL1 YV Y48 HR0 HK0 DI0 F1 F2).
  Qed.
End Arm.
End FPX_1.
