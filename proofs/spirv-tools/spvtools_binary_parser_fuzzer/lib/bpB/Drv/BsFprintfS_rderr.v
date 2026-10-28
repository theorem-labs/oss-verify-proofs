(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BHoare BFrame BShapeLaws BpecConsts BAgentLib BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BSymDriveH4 BSymAux BLibKnowFrame BMemSplit BLibTail BRefMemcpyLib BReach BegsEquivM BainEqv BeapCeil BazyRestrict BazySR BainMem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BArr BStep BLFrame BMState BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 B6_rip B6_istrlen BsLazyRun BsPrintfFirst BsSxKit BsScLib BsDrvMem BsDrvCells BsStrnlenK.
Import ListNotations.
Import BSymExec2.SX2. Import BSymExec2Sound.SX2S.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition FP_FMT : Z := 0x1fb71.

Definition FP_FR : Z := 2600.
Definition AVFPRINTF : Z := 0x16e480.
Definition ARET_MEMSET : Z := 0xa79b4.
Definition AISTRLEN_CALL : Z := 0xa7da0.
Definition AISTRLEN_RET : Z := 0xa7da4.
Definition ARIP_RET : Z := 0xa7e38.
Definition STOPFP : list Z := [ARET_MEMSET; AISTRLEN_CALL; AVFPRINTF; ARIP].
Definition FUELFP : nat := 20000.
Definition PMAXF : Z := 2^18.

Definition fp_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 2 => EVar 0 | 11 => ELit FP_FMT
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

Definition fp_cells : list (Z * nat * Z) :=
  [(0x191038, 8%nat, 0x7fff8000); (0x191d18, 1%nat, 0x1); (0x191d19, 1%nat, 0x1); (0x222bbc, 1%nat, 0x1);
   (0x186fc8, 8%nat, 0x16e480);
   (0x7fffbf68, 8%nat, 0x0); (0x7fffbf70, 8%nat, 0x0); (0x7fffac48, 8%nat, 0x0); (0x7fffac50, 8%nat, 0x0)].

Definition shwPA : expr := EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EVar 14) (ELit 3)) (ELit 2147450880)) (ELit (-8)).
Definition shwPB : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 1) (EVar 14)) (ELit 3)) (ELit 2147450880)) (ELit (-8)).

Definition fp_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (- FP_FR)) FP_FR;
   KRange (EVar 14) AHI_LO AAPP_HI; KRange (EVar 1) 0 PMAXF;
   KImg 0x10000 0x91000; KImg 0x17e000 0x186000;
   KZero (SA shwPA 0) (ELit 8); KZero (SA shwPB 0) (ELit 8)]
  ++ kn_cells fp_cells.

Definition in_dirwin (k : kentry) : bool :=
  match k with
  | KWord (SA (EVar 0) o) 1 _ => ((-2328 <=? o) && (o <? -2288))
  | _ => false
  end.
Definition repack (kn : list kentry) : list kentry := KZero (SA (EVar 0) (-2328)) (ELit 40) :: List.filter (fun k => negb (in_dirwin k)) kn.

Fixpoint has_zero_byte (kn : list kentry) (o : Z) : bool :=
  match kn with
  | [] => false
  | KWord (SA (EVar 0) o') 1 (ELit 0) :: r => Z.eqb o o' || has_zero_byte r o
  | _ :: r => has_zero_byte r o
  end.
Definition repack_ok (kn : list kentry) : bool := forallb (fun i => has_zero_byte kn (-2328 + Z.of_nat i)) (seq 0 40).

Definition fp_r1a := Eval vm_compute in (sym_exec RSEGS FUELFP true STOPFP (SCR [false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] [] []) (SS 0xa36d0 fp_sr [] fp_kn 34) []).
Definition fp_c1a := Eval vm_compute in (carry (s_log (fst (fst fp_r1a))) fp_kn []).
Definition fp_sr1a : list expr := Eval vm_compute in (s_regs (fst (fst fp_r1a))).
Definition fp_scs1a : list sidecond := Eval vm_compute in (snd (fst fp_r1a)).
Definition fp_kn1b : list kentry := Eval vm_compute in (repack (fst (fst fp_c1a))).

Definition fp_r1b := Eval vm_compute in (sym_exec RSEGS FUELFP true STOPFP scr0 (SS ARET_MEMSET fp_sr1a [] fp_kn1b 34) []).
Definition fp_c1b := Eval vm_compute in (carry (s_log (fst (fst fp_r1b))) fp_kn1b []).
Definition fp_sr1b : list expr := Eval vm_compute in (s_regs (fst (fst fp_r1b))).
Definition fp_kn2 : list kentry := Eval vm_compute in (fst (fst fp_c1b)).

Definition fp_r2 := Eval vm_compute in (sym_exec RSEGS FUELFP true [istrlen_entry] scr0 (SS AISTRLEN_CALL fp_sr1b [] fp_kn2 34) []).
Definition fp_sr2 : list expr := Eval vm_compute in (s_regs (fst (fst fp_r2))).

Definition fp_sr3 : list expr := Eval vm_compute in
  (map (fun i => match i with 10 => EVar 1 | 11 => EAlu ALU_ADD (EVar 1) (ELit 1) | 12 => ELit 0 | _ => nth i fp_sr2 (ELit 0) end)%nat (seq 0 32)).

Definition fp_kn3q : list kentry := Eval vm_compute in (KRange (EVar 1) 0 63 :: fp_kn2).
Definition fp_kn3s : list kentry := Eval vm_compute in (KRange (EVar 1) 64 PMAXF :: fp_kn2).

Definition fp_r3q := Eval vm_compute in (sym_exec RSEGS FUELFP true STOPFP (SCR [false; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] [] []) (SS AISTRLEN_RET fp_sr3 [] fp_kn3q 34) []).
Definition fp_c3q := Eval vm_compute in (carry (s_log (fst (fst fp_r3q))) fp_kn3q []).
Definition fp_sr3q : list expr := Eval vm_compute in (s_regs (fst (fst fp_r3q))).
Definition fp_scs3q : list sidecond := Eval vm_compute in (snd (fst fp_r3q)).
Definition fp_kn4q : list kentry := Eval vm_compute in (repack (fst (fst fp_c3q))).

Definition fp_r4q := Eval vm_compute in (sym_exec RSEGS FUELFP true STOPFP scr0 (SS ARET_MEMSET fp_sr3q [] fp_kn4q 34) []).
Definition fp_c4q := Eval vm_compute in (carry (s_log (fst (fst fp_r4q))) fp_kn4q []).
Definition fp_srFq : list expr := Eval vm_compute in (s_regs (fst (fst fp_r4q))).
Definition fp_knFq : list kentry := Eval vm_compute in (fst (fst fp_c4q)).

Definition fp_r3s := Eval vm_compute in (sym_exec RSEGS FUELFP true STOPFP (SCR [false] [] []) (SS AISTRLEN_RET fp_sr3 [] fp_kn3s 34) []).
Definition fp_c3s := Eval vm_compute in (carry (s_log (fst (fst fp_r3s))) fp_kn3s []).
Definition fp_sr3s : list expr := Eval vm_compute in (s_regs (fst (fst fp_r3s))).
Definition fp_scs3s : list sidecond := Eval vm_compute in (snd (fst fp_r3s)).
Definition fp_kn3s' : list kentry := Eval vm_compute in (fst (fst fp_c3s)).

Definition fp_sr4s : list expr := Eval vm_compute in (after_rip 34 fp_sr3s).
Definition fp_kn4se : list kentry := Eval vm_compute in (kn_cut 0 (-2432) (-2352) 0x100000000 fp_kn3s').

Definition fp_r4s := Eval vm_compute in (sym_exec RSEGS FUELFP true STOPFP (SCR [false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] [] []) (SS ARIP_RET fp_sr4s [] fp_kn4se 66) []).
Definition fp_c4s := Eval vm_compute in (carry (s_log (fst (fst fp_r4s))) fp_kn4se []).
Definition fp_sr4s' : list expr := Eval vm_compute in (s_regs (fst (fst fp_r4s))).
Definition fp_scs4s : list sidecond := Eval vm_compute in (snd (fst fp_r4s)).
Definition fp_kn5s : list kentry := Eval vm_compute in (repack (fst (fst fp_c4s))).

Definition fp_r5s := Eval vm_compute in (sym_exec RSEGS FUELFP true STOPFP scr0 (SS ARET_MEMSET fp_sr4s' [] fp_kn5s 66) []).
Definition fp_c5s := Eval vm_compute in (carry (s_log (fst (fst fp_r5s))) fp_kn5s []).
Definition fp_srFs : list expr := Eval vm_compute in (s_regs (fst (fst fp_r5s))).
Definition fp_knFs : list kentry := Eval vm_compute in (fst (fst fp_c5s)).

Lemma fp_itinerary :
  s_pc (fst (fst fp_r1a)) = ARET_MEMSET /\ snd (fst fp_r1a) = fp_scs1a /\ snd (fst fp_c1a) = [] /\ repack_ok (fst (fst fp_c1a)) = true
  /\ s_pc (fst (fst fp_r1b)) = AISTRLEN_CALL /\ snd (fst fp_r1b) = [] /\ snd (fst fp_c1b) = []
  /\ s_pc (fst (fst fp_r2)) = istrlen_entry /\ snd (fst fp_r2) = [] /\ s_log (fst (fst fp_r2)) = []
  /\ s_pc (fst (fst fp_r3q)) = ARET_MEMSET /\ snd (fst fp_r3q) = fp_scs3q /\ snd (fst fp_c3q) = [] /\ repack_ok (fst (fst fp_c3q)) = true
  /\ s_pc (fst (fst fp_r4q)) = AVFPRINTF /\ snd (fst fp_r4q) = [] /\ snd (fst fp_c4q) = []
  /\ s_pc (fst (fst fp_r3s)) = ARIP /\ snd (fst fp_r3s) = fp_scs3s /\ snd (fst fp_c3s) = []
  /\ s_pc (fst (fst fp_r4s)) = ARET_MEMSET /\ snd (fst fp_r4s) = fp_scs4s /\ snd (fst fp_c4s) = [] /\ repack_ok (fst (fst fp_c4s)) = true
  /\ s_pc (fst (fst fp_r5s)) = AVFPRINTF /\ snd (fst fp_r5s) = [] /\ snd (fst fp_c5s) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition fp_regions : list sregion := [(SA (EVar 0) (- FP_FR), FP_FR)].
Lemma fp_cov1a : log_covered fp_regions (s_log (fst (fst fp_r1a))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_cov1b : log_covered fp_regions (s_log (fst (fst fp_r1b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_cov3q : log_covered fp_regions (s_log (fst (fst fp_r3q))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_cov4q : log_covered fp_regions (s_log (fst (fst fp_r4q))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_cov3s : log_covered fp_regions (s_log (fst (fst fp_r3s))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_cov4s : log_covered fp_regions (s_log (fst (fst fp_r4s))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_cov5s : log_covered fp_regions (s_log (fst (fst fp_r5s))) = true. Proof. vm_compute. reflexivity. Qed.

Lemma fp_scs_ok : forall vals M (sp pp : word) (P : Z) scs,
  vals_ev vals 0 = sp -> vals_ev vals 14 = pp -> vals_ev vals 1 = Z_to_bv 64 P ->
  ASP_LO <= bv_unsigned sp -> bv_unsigned sp <= ASP_HI -> bv_unsigned sp mod 16 = 0 ->
  AHI_LO <= bv_unsigned pp -> bv_unsigned pp + P + 1 + 8 <= AAPP_HI -> 0 <= P ->
  In scs [fp_scs1a; fp_scs3q; fp_scs3s; fp_scs4s] ->
  scs_denot RSEGS M (ENV vals) scs.
Proof.
  intros vals M sp pp P scs P0 P14 P1 Hlo Hhi Hal Hplo Hphi HP Hin. unfold ASP_LO, ASP_HI, AHI_LO, AAPP_HI in *.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range pp) as Rpp.
  assert (XR : bv_unsigned (alu64 ALU_XOR pp (Z_to_bv 64 (-1))) = 2^64 - 1 - bv_unsigned pp).
  { cbn [alu64 alu]. rewrite bv_xor_unsigned. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
    rewrite B6_tac.lxor_ones64 by lia. lia. }
  assert (K1 : bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 P) (Z_to_bv 64 1)) = P + 1).
  { rewrite alu_add, vadd_wZ. unorm. lia. }
  cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold fp_scs1a, fp_scs3q, fp_scs3s, fp_scs4s, scs_denot;
    repeat (apply Forall_cons; [cbn [sc_denot edenot ev ENV]; rewrite ?P0, ?P14, ?P1 |]); try apply Forall_nil;
    first [ asc_br | cbn [branch_taken]; unfold bv_ltu; rewrite XR, K1; apply Z.ltb_ge; lia ].
Qed.

Lemma has_zero_byte_sound : forall E M kn o, know_ok RSEGS E M kn -> has_zero_byte kn o = true ->
  kentry_ok RSEGS E M (KWord (SA (EVar 0) o) 1 (ELit 0)).
Proof.
  intros E M kn o HK Hb. induction kn as [|k r IH]; [discriminate|].
  apply Forall_cons_iff in HK as [H1 H2]. cbn [has_zero_byte] in Hb.
  destruct k as [[[z|i| | | | | |] o'] w v| | | | | | |]; try (apply IH; assumption).
  destruct i; [|apply IH; assumption]. destruct w as [|[|w]]; try (apply IH; assumption).
  destruct v as [z| | | | | | |]; try (apply IH; assumption). destruct z; try (apply IH; assumption).
  apply orb_prop in Hb as [Hb|Hb]; [|apply IH; assumption]. apply Z.eqb_eq in Hb. subst o'. exact H1.
Qed.

Lemma rdn1_high : forall M (a : Z) (b : byte),
  rdn RSEGS M (Z_to_bv 64 a) 1 = Some [b] -> 0x6e8000 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) = Some b.
Proof.
  intros M a b RD Ha. cbn [rdn] in RD. destruct (M (Z_to_bv 64 a)) as [b'|] eqn:E.
  - cbn in RD. congruence.
  - rewrite (aseg_rom_high (Z_to_bv 64 a)) in RD; [discriminate|]. rewrite u_small by lia. lia.
Qed.

Lemma know_repack : forall vals M kn (sp : word),
  vals_ev vals 0 = sp -> ASP_LO <= bv_unsigned sp -> bv_unsigned sp <= ASP_HI ->
  know_ok RSEGS (ENV vals) M kn -> repack_ok kn = true -> know_ok RSEGS (ENV vals) M (repack kn).
Proof.
  intros vals M kn sp P0 Hlo Hhi HK HR. unfold ASP_LO, ASP_HI in *. pose proof (u64_range sp) as Rsp. unfold repack. apply know_ok_cons.
  - eapply (kzero_intro RSEGS _ M (EVar 0) sp (-2328) (ELit 40) 40); [cbn [edenot ev ENV]; exact P0 | reflexivity | lia | lia | lia |].
    intros i Hi.
    assert (HB : has_zero_byte kn (-2328 + i) = true).
    { unfold repack_ok in HR.
      assert (IN : forall l, forallb (fun j => has_zero_byte kn (-2328 + Z.of_nat j)) l = true ->
                   forall m, In m l -> has_zero_byte kn (-2328 + Z.of_nat m) = true).
      { induction l as [|x l IH]; intros Hf m Hm; [destruct Hm|]. cbn [forallb] in Hf. apply andb_prop in Hf as [Hx Hl].
        destruct Hm as [<-|Hm]; [exact Hx | apply IH; assumption]. }
      replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (IN (seq 0 40) HR). apply in_seq. lia. }
    pose proof (has_zero_byte_sound _ M kn _ HK HB) as (_ & _ & RD).
    unfold adenot, v_addi in RD. cbn [a_base a_off edenot ev ENV] in RD. rewrite P0 in RD.
    replace (bv_unsigned sp + (-2328 + i)) with (bv_unsigned sp + -2328 + i) in RD by lia.
    exact (rdn1_high M _ _ RD ltac:(lia)).
  - unfold know_ok in *. apply Forall_forall. intros k Hk. apply List.filter_In in Hk as [Hk _]. exact (proj1 (Forall_forall _ _) HK k Hk).
Qed.

Lemma fp_cells_of : forall m, ACONST m -> cells_ok m fp_cells.
Proof.
  intros m AC. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2];
    change (AINITED_CELL + 1) with 1645849 in I2 end.
  lazymatch goal with X : rw_cells asegs m ACF_CHKPRINTF_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I3 end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_OPEN _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_OPEN 0 0 X ltac:(unfold ASHW_MSG_OPEN; lia) ltac:(unfold ASHW_MSG_OPEN; lia)) as [S1 S2];
    change (ASHW_MSG_OPEN + 8) with 2147467120 in S2 end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_USAGE _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_USAGE 0 0 X ltac:(unfold ASHW_MSG_USAGE; lia) ltac:(unfold ASHW_MSG_USAGE; lia)) as [S3 S4];
    change (ASHW_MSG_USAGE + 8) with 2147462224 in S4 end.
  unfold fp_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | exact S1 | exact S2 | exact S3 | exact S4
          | unfold cell_ok; first [exact I1 | exact I2 | exact I3] ].
Qed.

Lemma fp_rdn_bytes_at : forall bs m (a : Z),
  rdn RSEGS m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at asegs m a bs.
Proof.
  induction bs as [|b bs IH]; intros m a HR Ha Hn.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [length] in HR, Hn. cbn [rdn] in HR. fold (rdn RSEGS m) in HR.
    destruct (match m (Z_to_bv 64 a) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b'|] eqn:Hm; [|discriminate].
    destruct (rdn RSEGS m (Z_to_bv 64 a + 1) (length bs)) as [r|] eqn:Hr; [|discriminate]. injection HR as <- <-.
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. unfold mrd, wa. exact Hm.
    + cbn [nth_error]. destruct (Z.eq_dec (a + 1) (2 ^ 64)) as [Heq|Hne]. { cbn [length] in Hi. lia. }
      assert (Ea : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
      { apply bv_eq. rewrite u_add1 by (rewrite u_small by lia; lia). rewrite !u_small by lia. reflexivity. }
      rewrite Ea in Hr. pose proof (IH m (a + 1) Hr ltac:(lia) ltac:(cbn [length] in Hi |- *; lia)) as (_ & _ & IHi).
      replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IHi. cbn [length] in Hi. lia.
Qed.

Section Plain.
  Variables (L S Zr : list (word * word)).

  Record fpH (regs : bvmap 5 word) (mem : word -> option byte) (sp pp ra : word) (str : list byte) : Prop := FPH {
    G1  : getr regs 1 = ra;
    G2  : getr regs 2 = sp;
    G11 : getr regs 11 = Z_to_bv 64 FP_FMT;
    G12 : getr regs 12 = pp;
    Hsp16 : bv_unsigned sp mod 16 = 0;
    HspLo : ASP_LO <= bv_unsigned sp;
    HspHi : bv_unsigned sp <= ASP_HI;
    Hstk  : stk asegs mem (bv_unsigned sp - FP_FR) (bv_unsigned sp);
    Hgot  : forall i, 0x17e000 <= i < 0x186000 -> mem (Z_to_bv 64 i) = None;
    Hac   : ACONST mem;
    Hinv  : mem_inv asegs mem;

    Hstr  : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned pp)) (length str + 1) = Some (str ++ [Z_to_bv 8 0]);
    Hnonul : ~ In (Z_to_bv 8 0) str;
    HpLo  : AHI_LO <= bv_unsigned pp;
    HpHi  : bv_unsigned pp + Z.of_nat (length str) + 1 + 8 <= AAPP_HI;
    HPmax : Z.of_nat (length str) + 1 < PMAXF;
    Hdisj : bv_unsigned pp + Z.of_nat (length str) + 1 <= bv_unsigned sp - FP_FR \/ bv_unsigned sp <= bv_unsigned pp;

    Fsh0  : forall a, shw8 (bv_unsigned pp) <= a < shw8 (bv_unsigned pp + Z.of_nat (length str)) + 8 -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0) }.

  Record fpPost (regs : bvmap 5 word) (mem : word -> option byte) (sp pp ra : word)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := FPP {
    P_sp  : getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 112);
    P_ra  : getr regs' 1 = Z_to_bv 64 0xa8c60;
    P_a0  : getr regs' 10 = getr regs 10;
    P_a1  : getr regs' 11 = Z_to_bv 64 FP_FMT;
    P_a2  : getr regs' 12 = Z_to_bv 64 (bv_unsigned sp - 48);

    P_s0  : getr regs' 8 = Z_to_bv 64 FP_FMT;
    P_s1  : getr regs' 9 = getr regs 10;
    P_s2  : getr regs' 18 = Z_to_bv 64 (bv_unsigned sp - 48);
    P_cs  : forall r : reg, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - FP_FR), FP_FR)];
    P_va0 : rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 48)) 8 = Some (word_to_le_bytes 8 pp);
    P_sra : rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 56)) 8 = Some (word_to_le_bytes 8 ra);
    P_ss0 : rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 8));
    P_ss1 : rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 9));
    P_ss2 : rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 18));
    P_stk : stk asegs mem' (bv_unsigned sp - FP_FR) (bv_unsigned sp);
    P_inv : mem_inv asegs mem';
    P_ac  : ACONST mem' }.

  Definition fp_vals (regs : bvmap 5 word) (sp : word) (P : Z) : list word := [sp; Z_to_bv 64 P] ++ junk_vals regs.

  Lemma fp_ev_junk : forall regs sp P i, (2 <= i < 34)%nat ->
    ev (ENV (fp_vals regs sp P)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    intros regs sp P i Hi. unfold ENV, fp_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 P] + (i - 2))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma fp_regs_ok : forall regs mem sp pp ra str, fpH regs mem sp pp ra str ->
    regs_ok (ENV (fp_vals regs sp (Z.of_nat (length str)))) fp_sr regs.
  Proof.
    intros regs mem sp pp ra str PH. destruct PH.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth fp_sr allregs32 edenot].
    1: apply getr_zero.
    2: cbn [ev ENV]; assumption.
    10: assumption.
    all: rewrite fp_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma fp_know_ok : forall regs mem sp pp ra str, fpH regs mem sp pp ra str ->
    know_ok RSEGS (ENV (fp_vals regs sp (Z.of_nat (length str)))) mem fp_kn.
  Proof.
    intros regs mem sp pp ra str PH.
    destruct PH as [HR1 HR2 HR11 HR12 Hsp16 HspLo HspHi Hstk Hgot Hac Hinv Hstr Hnonul HpLo HpHi HPmax Hdisj Fsh0].
    pose proof (u64_range sp) as Hsp. pose proof (u64_range pp) as Hpp. set (P := Z.of_nat (length str)) in *.
    unfold AHI_LO, AAPP_HI, ASP_LO, ASP_HI, PMAXF in *.
    assert (E0 : ev (ENV (fp_vals regs sp P)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (fp_vals regs sp P)) 1 = Z_to_bv 64 P) by reflexivity.
    assert (E14 : ev (ENV (fp_vals regs sp P)) 14 = pp) by (rewrite fp_ev_junk by lia; exact HR12).
    assert (DA' : bv_unsigned (edenot (ENV (fp_vals regs sp P)) shwPA) = shw8 (bv_unsigned pp)).
    { unfold shwPA, shw8. cbn [edenot]. rewrite E14. cbn [alu64 alu].
      rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, !Z_to_bv_unsigned.
      change (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      change (2147450880 mod 2 ^ 64) with 2147450880. change ((-8) mod 2 ^ 64) with 18446744073709551608.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite ASHADOW_BASE_val.
      rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). reflexivity. }
    assert (DB' : bv_unsigned (edenot (ENV (fp_vals regs sp P)) shwPB) = shw8 (bv_unsigned pp + P)).
    { unfold shwPB, shw8. cbn [edenot]. rewrite E14, E1. cbn [alu64 alu].
      rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
      change (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      change (2147450880 mod 2 ^ 64) with 2147450880. change ((-8) mod 2 ^ 64) with 18446744073709551608.
      rewrite (Z.mod_small P) by lia. rewrite (Z.mod_small (P + _)) by lia.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite ASHADOW_BASE_val.
      rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). rewrite (Z.add_comm P). reflexivity. }
    pose proof (shw8_range (bv_unsigned pp) ltac:(unfold AAPP_HI; lia)) as (A1 & A2 & A3).
    pose proof (shw8_range (bv_unsigned pp + P) ltac:(unfold AAPP_HI; lia)) as (B1 & B2 & B3).
    pose proof (shw8_mono (bv_unsigned pp) (bv_unsigned pp + P) ltac:(lia)) as AB.
    rewrite ASHADOW_BASE_val in A1, B1. unfold AHI_LO in A2, B2.
    unfold fp_kn. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
    2:{ apply cells_know; [vm_compute; reflexivity | apply fp_cells_of; assumption]. }
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp FP_FR); [exact E0 | | unfold FP_FR; lia].
      eapply astk_stk_ok; [exact Hstk | lia | lia | unfold FP_FR; lia | lia].
    - apply krange_intro. cbn [edenot]. rewrite E14. unfold AHI_LO, AAPP_HI. lia.
    - apply krange_intro. cbn [edenot]. rewrite E1, u_small by lia. unfold PMAXF. lia.
    - apply kimg_intro; [lia | lia | apply (amem_inv_ro_none mem Hinv)].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kzero_intro RSEGS _ mem shwPA (edenot _ shwPA) 0 (ELit 8) 8); [reflexivity | reflexivity | lia | lia | rewrite DA'; lia |].
      intros i Hi. rewrite DA'. apply Fsh0. lia.
    - eapply (kzero_intro RSEGS _ mem shwPB (edenot _ shwPB) 0 (ELit 8) 8); [reflexivity | reflexivity | lia | lia | rewrite DB'; lia |].
      intros i Hi. rewrite DB'. apply Fsh0. lia.
  Qed.

  Definition fp_regions_w (sp : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - FP_FR), FP_FR)].

  Lemma fp_regions_denot : forall vals sp, vals_ev vals 0 = sp -> ASP_LO <= bv_unsigned sp ->
    map (rdenot (ENV vals)) fp_regions = fp_regions_w sp.
  Proof.
    intros vals sp P0 Hlo. unfold ASP_LO in Hlo. unfold fp_regions, fp_regions_w, rdenot, estart, FP_FR.
    cbn [map fst snd a_base a_off edenot ev ENV]. rewrite P0. repeat f_equal; lia.
  Qed.

  Lemma fp_regions_flat : forall vals sp, vals_ev vals 0 = sp -> ASP_LO <= bv_unsigned sp -> bv_unsigned sp <= ASP_HI ->
    regions_flat (ENV vals) fp_regions.
  Proof.
    intros vals sp P0 Hlo Hhi r Hr. unfold ASP_LO, ASP_HI in *. unfold fp_regions, FP_FR in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma fp_mem_frame : forall regs mem sp pp ra str m',
    fpH regs mem sp pp ra str -> frame_mod mem m' (fp_regions_w sp) ->
    stk asegs m' (bv_unsigned sp - FP_FR) (bv_unsigned sp) /\ mem_inv asegs m' /\ ACONST m'
    /\ rdn RSEGS m' (Z_to_bv 64 (bv_unsigned pp)) (length str + 1) = Some (str ++ [Z_to_bv 8 0])
    /\ (forall a, shw8 (bv_unsigned pp) <= a < shw8 (bv_unsigned pp + Z.of_nat (length str)) + 8 -> m' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  Proof.
    intros regs mem sp pp ra str m' PH FM.
    destruct PH as [HR1 HR2 HR11 HR12 Hsp16 HspLo HspHi Hstk Hgot Hac Hinv Hstr Hnonul HpLo HpHi HPmax Hdisj Fsh0].
    pose proof (u64_range sp) as Hsp. pose proof (u64_range pp) as Hpp. set (P := Z.of_nat (length str)) in *.
    unfold ASP_LO, ASP_HI, AHI_LO, AAPP_HI in *.
    pose proof (shw8_range (bv_unsigned pp) ltac:(unfold AAPP_HI; lia)) as (A1 & A2 & A3).
    pose proof (shw8_range (bv_unsigned pp + P) ltac:(unfold AAPP_HI; lia)) as (B1 & B2 & B3).
    rewrite ASHADOW_BASE_val in A1, B1. unfold AHI_LO in A2, B2.
    split; [|split; [|split; [|split]]].
    - eapply astk_grows; [exact Hstk | unfold FP_FR; lia | lia | exact (proj2 FM)].
    - eapply amem_inv_frame; [exact Hinv | exact FM |]. constructor; [|constructor]. cbn [fst snd]. unfold FP_FR. rewrite u_small by lia. lia.
    - eapply ACONST_frame; [exact Hac | apply frame_mod_munch; exact FM | apply (aframe_mod_wmono _ _ _ FM) |].
      unfold ivls, fp_regions_w. cbn [map fst snd]. unfold FP_FR. rewrite u_small by lia.
      constructor; [|constructor]. apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; change (7241728 / 8) with 905216; lia | lia].
    - eapply ardn_frame; [exact FM | exact Hstr | lia | lia |].
      intros r Hr. destruct Hr as [<-|[]]. cbn [fst snd]. unfold FP_FR in *. rewrite u_small by lia. lia.
    - intros a Ha. rewrite (proj1 FM); [apply Fsh0; exact Ha|]. cbn [outside]. split; [|exact I].
      unfold in_rng, FP_FR. rewrite !u_small by lia. lia.
  Qed.

  Lemma fp_frame_mod_of_munch : forall m m' (l h : Z) (sp : word),
    munch [(l, h)] m m' -> mem_grows m m' -> bv_unsigned sp - FP_FR <= l -> h <= bv_unsigned sp -> FP_FR <= bv_unsigned sp ->
    frame_mod m m' (fp_regions_w sp).
  Proof.
    intros m m' l h sp MU MG Hl Hh Hsp. pose proof (u64_range sp). split; [|exact MG].
    intros a Ha. apply MU. cbn [outside fp_regions_w] in Ha |- *. destruct Ha as [Ha _]. unfold in_rng, FP_FR in *.
    rewrite u_small in Ha by lia. split; [|exact I]. lia.
  Qed.

  Ltac fp_regs_after_rip HR vals HL Rn srn HRn :=
    let HRj := fresh "HRj" in
    lazymatch type of HR with regs_ok _ ?sr ?R0 =>
      pose proof (regs_after_keeps vals (blobs_ev []) sr R0 Rn rip_kept ltac:(rewrite HL; vm_compute; reflexivity) HR) as HRj end;
    lazymatch type of HRj with ?KE -> ?N0 -> _ =>
      assert (KEPT : KE) by (intros r Hr; cbn [In rip_kept] in Hr;
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]]]]]; reflexivity);
      specialize (HRj KEPT rip_kept_no0); clear KEPT
    end;
    rewrite HL in HRj;
    change (Env (vals_ev (vals ++ junk_vals Rn)) (blobs_ev [])) with (ENV (vals ++ junk_vals Rn)) in HRj;
    assert (HRn : regs_ok (ENV (vals ++ junk_vals Rn)) srn Rn);
    [ intros r; destruct (bv_eq_dec 5 r 10%bv) as [->|NE];
      [ reflexivity
      | rewrite (HRj r); destruct (reg_of_nat r) as (n & -> & Hn);
        do 32 (destruct n as [|n]; [first [reflexivity | exfalso; apply NE; apply bv_eq; reflexivity] |]); lia ]
    | clear HRj ].

  Ltac fp_block r c CC scr pc sr kn nx E M R msF mo HR HK SCS OK RS :=
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELFP STOPFP scr pc sr kn nx (fst (fst r)) (snd (fst r)) (snd r)
              (fst (fst c)) (snd (fst c)) (snd c) E M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ r) | vm_cast_no_check (@eq_refl _ c)
      | exact HR | exact HK | SCS | rewrite CC; constructor | exact OK | exact RS | ].

  Theorem as_fprintf_rderr_k : forall regs mem msF mo (sp pp ra : word) (str : list byte) (KX : TSet),
    fpH regs mem sp pp ra str ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xa36d0) mem (seg_rom RSEGS) ->
    (forall regs' mem' msF' mo', fpPost regs mem sp pp ra regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 AVFPRINTF) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') KX) ->
    realizes RSEGS (mkCfg msF mo) KX.
  Proof.
    intros regs mem msF mo sp pp ra str KX PH OK RS HCONT. pose proof PH as PH0.
    pose proof (fp_regs_ok regs mem sp pp ra str PH) as HR. pose proof (fp_know_ok regs mem sp pp ra str PH) as HK.
    destruct PH as [G1 G2 G11 G12 Hsp16 HspLo HspHi Hstk Hgot Hac Hinv Hstr Hnonul HpLo HpHi HPmax Hdisj Fsh0].
    pose proof (u64_range sp) as Hsp. pose proof (u64_range pp) as Hpp. set (P := Z.of_nat (length str)) in *.
    unfold ASP_LO, ASP_HI, AHI_LO, AAPP_HI, PMAXF in *.
    set (vals := fp_vals regs sp P) in *.
    assert (HL : length vals = 34%nat) by (subst vals; unfold fp_vals; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp) by reflexivity.
    assert (P1 : vals_ev vals 1 = Z_to_bv 64 P) by reflexivity.
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))) by (intros i Hi; subst vals; apply (fp_ev_junk regs sp P i Hi)).
    assert (P14 : vals_ev vals 14 = pp) by (rewrite PJ by lia; exact G12).
    assert (P3 : vals_ev vals 3 = ra) by (rewrite PJ by lia; exact G1).
    pose proof (fp_regions_flat vals sp P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF.
    pose proof (fp_regions_denot vals sp P0 ltac:(unfold ASP_LO; lia)) as RD.
    pose proof fp_itinerary as (PC1a & SC1a & CC1a & RP1a & PC1b & SC1b & CC1b & PC2 & SC2 & LG2 & PC3q & SC3q & CC3q & RP3q
                                & PC4q & SC4q & CC4q & PC3s & SC3s & CC3s & PC4s & SC4s & CC4s & RP4s & PC5s & SC5s & CC5s).
    Ltac scs_by vals M P0 P14 P1 :=
      apply (fp_scs_ok vals M _ _ _ _ P0 P14 P1); [unfold ASP_LO; lia | unfold ASP_HI; lia | assumption | unfold AHI_LO; lia | unfold AAPP_HI; lia | lia | cbn; tauto].

    assert (POST : forall (valsX : list word) RX MX msFX moX (srX : list expr) (knX : list kentry),
      (forall i, (i < 34)%nat -> vals_ev valsX i = vals_ev vals i) ->
      regs_ok (ENV valsX) srX RX -> know_ok RSEGS (ENV valsX) MX knX ->
      (srX = fp_srFq /\ knX = fp_knFq) \/ (srX = fp_srFs /\ knX = fp_knFs) ->
      frame_mod mem MX (fp_regions_w sp) ->
      lzok RSEGS L S Zr (mkCfg msFX moX) -> same_but_materialized mo moX -> hid_same L S msF msFX ->
      restrict L S msFX = mkst RX (Z_to_bv 64 AVFPRINTF) MX (seg_rom RSEGS) ->
      realizes RSEGS (mkCfg msFX moX) KX).
    { intros valsX RX MX msFX moX srX knX QV HRX HKX HX F OKX SBX HSX RSX.
      destruct (fp_mem_frame regs mem sp pp ra str MX PH0 F) as (STX & INVX & ACX & _ & _).
      assert (QJ : forall i, (2 <= i < 34)%nat -> vals_ev valsX i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))).
      { intros i Hi. rewrite QV by lia. apply PJ. exact Hi. }
      assert (X0 : vals_ev valsX 0 = sp) by (rewrite QV by lia; exact P0).
      assert (X14 : vals_ev valsX 14 = pp) by (rewrite QV by lia; exact P14).
      apply (HCONT RX MX msFX moX); try assumption.
      destruct HX as [[-> ->] | [-> ->]]; split; try assumption;
        first [ regv HRX (2%bv : reg); cbn [edenot ev ENV]; rewrite X0, alu_add, vadd_wZ; f_equal; lia
              | regv HRX (1%bv : reg); reflexivity
              | regv HRX (10%bv : reg); cbn [edenot ev ENV]; rewrite QJ by lia; reflexivity
              | regv HRX (11%bv : reg); reflexivity
              | regv HRX (12%bv : reg); cbn [edenot ev ENV]; rewrite X0, alu_add, vadd_wZ; f_equal; lia
              | regv HRX (8%bv : reg); reflexivity
              | regv HRX (9%bv : reg); cbn [edenot ev ENV]; rewrite QJ by lia; reflexivity
              | regv HRX (18%bv : reg); cbn [edenot ev ENV]; rewrite X0, alu_add, vadd_wZ; f_equal; lia
              | intros r Hr; cbn [In] in Hr;
                destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
                lazymatch goal with |- getr RX ?rr = _ => regv HRX rr end; cbn [edenot ev ENV]; rewrite QJ by lia; f_equal; apply bv_eq; reflexivity
              | let Hc := fresh "Hc" in
                lazymatch goal with |- rdn _ _ (Z_to_bv 64 (bv_unsigned sp - ?k)) 8%nat = Some _ =>
                  krdv HKX 0%nat (- k) 8%nat Hc;
                  [ unfold flat, estart; cbn [a_base a_off edenot ev ENV]; rewrite X0; lia
                  | unfold adenot, v_addi in Hc; cbn [a_base a_off edenot ev ENV] in Hc; rewrite X0 in Hc;
                    replace (bv_unsigned sp + - k) with (bv_unsigned sp - k) in Hc by lia; rewrite Hc;
                    rewrite ?X14, ?QJ by lia; first [reflexivity | rewrite <- G1; do 3 f_equal; apply bv_eq; reflexivity | do 3 f_equal; apply bv_eq; reflexivity] ]
                end ]. }

    fp_block fp_r1a fp_c1a CC1a (SCR [false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] [] []) 0xa36d0 fp_sr fp_kn 34%nat (ENV vals) mem regs msF mo HR HK
             ltac:(rewrite SC1a; scs_by vals mem P0 P14 P1) OK RS.
    clear HR HK OK RS. intros R1 M1 msF1 mo1 HR HK EQ1 LF1 OK1 SB1 HS1 RS1.
    pose proof (log_covered_frame (ENV vals) mem fp_regions _ fp_cov1a RF LF1) as F1. rewrite <- EQ1, RD in F1.
    change (s_regs (fst (fst fp_r1a))) with fp_sr1a in HR. rewrite PC1a in RS1.
    pose proof (know_repack vals M1 _ sp P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia) HK RP1a) as HK'. clear HK.
    change (repack (fst (fst fp_c1a))) with fp_kn1b in HK'.

    fp_block fp_r1b fp_c1b CC1b scr0 ARET_MEMSET fp_sr1a fp_kn1b 34%nat (ENV vals) M1 R1 msF1 mo1 HR HK'
             ltac:(rewrite SC1b; constructor) OK1 RS1.
    clear HR HK' RS1. intros R2 M2 msF2 mo2 HR HK EQ2 LF2 OK2 SB2 HS2 RS2.
    pose proof (log_covered_frame (ENV vals) M1 fp_regions _ fp_cov1b RF LF2) as F2. rewrite <- EQ2, RD in F2.
    change (s_regs (fst (fst fp_r1b))) with fp_sr1b in HR. change (fst (fst fp_c1b)) with fp_kn2 in HK. rewrite PC1b in RS2.
    assert (F02 : frame_mod mem M2 (fp_regions_w sp)) by (eapply frame_mod_trans_same; [exact F1 | exact F2]).

    eapply (rz_run_lf_lazy RSEGS L S Zr FUELFP [istrlen_entry] scr0 AISTRLEN_CALL fp_sr1b fp_kn2 34 (fst (fst fp_r2)) (snd (fst fp_r2)) (snd fp_r2)
              fp_kn2 [] [] (ENV vals) M2 (seg_rom RSEGS) R2 msF2 mo2);
      [ vm_cast_no_check (@eq_refl _ fp_r2) | rewrite LG2; reflexivity
      | exact HR | exact HK | rewrite SC2; constructor | constructor | exact OK2 | exact RS2 | ].
    clear HR RS2. intros R3 M3 msF3 mo3 HR HK3 EQ3 _ OK3 SB3 HS3 RS3.
    rewrite LG2 in EQ3. cbn [mem_denot] in EQ3. subst M3. clear HK3.
    change (s_regs (fst (fst fp_r2))) with fp_sr2 in HR. rewrite PC2 in RS3.
    destruct (fp_mem_frame regs mem sp pp ra str M2 PH0 F02) as (ST2 & INV2 & AC2 & STR2 & SH2).

    assert (U1 : getr R3 1%bv = Z_to_bv 64 AISTRLEN_RET) by (regv HR (1%bv : reg); reflexivity).
    assert (U10 : getr R3 10%bv = pp) by (regv HR (10%bv : reg); cbn [edenot ev ENV]; exact P14).
    unfold getr in U1, U10. change (bv_eqb 1%bv 0%bv) with false in U1. change (bv_eqb 10%bv 0%bv) with false in U10. cbv iota in U1, U10.
    apply (lz_renorm L S Zr msF3 mo3 R3 _ M2 _ KX OK3 RS3). intros msFn OKn RSn HSn.
    apply (lz_evt L S Zr (istrlen_post (reg_get R3 1) (reg_get R3 2) (reg_get R3 3) (reg_get R3 4) (reg_get R3 5) (reg_get R3 6) (reg_get R3 7)
                     (reg_get R3 8) (reg_get R3 9) (reg_get R3 13) (reg_get R3 14) (reg_get R3 15) (reg_get R3 16) (reg_get R3 17)
                     (reg_get R3 18) (reg_get R3 19) (reg_get R3 20) (reg_get R3 21)
                     (reg_get R3 22) (reg_get R3 23) (reg_get R3 24) (reg_get R3 25) (reg_get R3 26) (reg_get R3 27)
                     (reg_get R3 28) (reg_get R3 29) (reg_get R3 30) (reg_get R3 31) bvmap_empty (Z_to_bv 32 0) P M2) msFn mo3 KX OKn).
    { rewrite RSn. unfold mkR_of. subst P.
      apply (istrlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M2 str []); [| exact Hnonul].
      rewrite U10. apply fp_rdn_bytes_at; [ | lia | rewrite length_app; cbn [length]; lia].
      rewrite length_app. cbn [length]. replace (length str + 1)%nat with (length str + 1)%nat by lia. exact STR2. }
    clear OKn RSn. intros msF4 mo4 OK4 SB4 HS4 HP4. unfold istrlen_post in HP4.
    assert (RP : ret_pc (reg_get R3 1) = Z_to_bv 64 AISTRLEN_RET) by (rewrite U1; unfold AISTRLEN_RET; apply ret_pc_even; [lia | reflexivity]).
    rewrite RP in HP4. clear RP.
    lazymatch type of HP4 with _ = MS ?Rx _ ?pcx _ _ _ ?romx =>
      change (restrict L S msF4 = mkst Rx pcx M2 romx) in HP4; set (R4 := Rx) in HP4 end.
    assert (Ga11 : getr R4 11%bv = Z_to_bv 64 (P + 1)) by reflexivity.
    assert (HR4 : regs_ok (ENV vals) fp_sr3 R4).
    { apply regs_ok_by_idx. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth fp_sr3 allregs32];
        first [ reflexivity
              | cbn [edenot ev ENV]; rewrite ?P1; first [reflexivity | rewrite alu_add, vadd_wZ; apply bv_eq; unorm; lia ]
              | rewrite Ga11; cbn [edenot ev ENV]; rewrite ?P1, alu_add, vadd_wZ; apply bv_eq; unorm; lia
              | lazymatch goal with |- getr R4 ?r = _ => transitivity (getr R3 r); [unfold getr; reflexivity | rewrite (HR r); reflexivity] end ]. }
    clear HR U1 U10 OK3 RS3.
    destruct (Z_lt_le_dec P 64) as [KQ|KS].
    -
      assert (HK3 : know_ok RSEGS (ENV vals) M2 fp_kn3q).
      { change fp_kn3q with (KRange (EVar 1) 0 63 :: fp_kn2). apply know_ok_cons; [|exact HK].
        apply krange_intro. cbn [edenot ev ENV]. rewrite P1, u_small by lia. lia. }
      clear HK.
      fp_block fp_r3q fp_c3q CC3q (SCR [false; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] [] []) AISTRLEN_RET fp_sr3 fp_kn3q 34%nat (ENV vals) M2 R4 msF4 mo4 HR4 HK3
               ltac:(rewrite SC3q; scs_by vals M2 P0 P14 P1) OK4 HP4.
      clear HR4 HK3. intros R5 M5 msF5 mo5 HR HK EQ5 LF5 OK5 SB5 HS5 RS5.
      pose proof (log_covered_frame (ENV vals) M2 fp_regions _ fp_cov3q RF LF5) as F5. rewrite <- EQ5, RD in F5.
      change (s_regs (fst (fst fp_r3q))) with fp_sr3q in HR. rewrite PC3q in RS5.
      pose proof (know_repack vals M5 _ sp P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia) HK RP3q) as HK'. clear HK.
      change (repack (fst (fst fp_c3q))) with fp_kn4q in HK'.
      fp_block fp_r4q fp_c4q CC4q scr0 ARET_MEMSET fp_sr3q fp_kn4q 34%nat (ENV vals) M5 R5 msF5 mo5 HR HK'
               ltac:(rewrite SC4q; constructor) OK5 RS5.
      clear HR HK' RS5. intros R6 M6 msF6 mo6 HR HK EQ6 LF6 OK6 SB6 HS6 RS6.
      pose proof (log_covered_frame (ENV vals) M5 fp_regions _ fp_cov4q RF LF6) as F6. rewrite <- EQ6, RD in F6.
      change (s_regs (fst (fst fp_r4q))) with fp_srFq in HR. change (fst (fst fp_c4q)) with fp_knFq in HK. rewrite PC4q in RS6.
      apply (POST vals R6 M6 msF6 mo6 fp_srFq fp_knFq ltac:(intros; reflexivity) HR HK ltac:(left; split; reflexivity)); try assumption.
      + eapply frame_mod_trans_same; [exact F02|]. eapply frame_mod_trans_same; [exact F5 | exact F6].
      + eapply same_but_materialized_trans; [exact SB1|]. eapply same_but_materialized_trans; [exact SB2|].
        eapply same_but_materialized_trans; [exact SB3|]. eapply same_but_materialized_trans; [exact SB4|].
        eapply same_but_materialized_trans; [exact SB5 | exact SB6].
      + eapply hid_same_trans; [exact HS1|]. eapply hid_same_trans; [exact HS2|]. eapply hid_same_trans; [exact HS3|].
        eapply hid_same_trans; [exact HSn|]. eapply hid_same_trans; [exact HS4|]. eapply hid_same_trans; [exact HS5 | exact HS6].
    -
      assert (HK3 : know_ok RSEGS (ENV vals) M2 fp_kn3s).
      { change fp_kn3s with (KRange (EVar 1) 64 PMAXF :: fp_kn2). apply know_ok_cons; [|exact HK].
        apply krange_intro. cbn [edenot ev ENV]. rewrite P1, u_small by lia. unfold PMAXF. lia. }
      clear HK.
      fp_block fp_r3s fp_c3s CC3s (SCR [false] [] []) AISTRLEN_RET fp_sr3 fp_kn3s 34%nat (ENV vals) M2 R4 msF4 mo4 HR4 HK3
               ltac:(rewrite SC3s; scs_by vals M2 P0 P14 P1) OK4 HP4.
      clear HR4 HK3. intros R5 M5 msF5 mo5 HR HK EQ5 LF5 OK5 SB5 HS5 RS5.
      pose proof (log_covered_frame (ENV vals) M2 fp_regions _ fp_cov3s RF LF5) as F5. rewrite <- EQ5, RD in F5.
      change (s_regs (fst (fst fp_r3s))) with fp_sr3s in HR. change (fst (fst fp_c3s)) with fp_kn3s' in HK. rewrite PC3s in RS5.
      assert (F05 : frame_mod mem M5 (fp_regions_w sp)) by (eapply frame_mod_trans_same; [exact F02 | exact F5]).
      destruct (fp_mem_frame regs mem sp pp ra str M5 PH0 F05) as (ST5 & INV5 & AC5 & _ & SH5).

      assert (U1 : getr R5 1%bv = Z_to_bv 64 ARIP_RET) by (regv HR (1%bv : reg); reflexivity).
      assert (U2 : bv_unsigned (getr R5 2%bv) = bv_unsigned sp - 2352).
      { regv HR (2%bv : reg). cbn [edenot ev ENV]. rewrite P0, alu_add, vadd_wZ. unorm. lia. }
      assert (U10 : getr R5 10%bv = pp) by (regv HR (10%bv : reg); cbn [edenot ev ENV]; exact P14).
      assert (U11 : bv_unsigned (getr R5 11%bv) = P + 1).
      { regv HR (11%bv : reg). cbn [edenot ev ENV]. rewrite P1, alu_add, vadd_wZ. unorm. lia. }
      unfold getr in U1, U2, U10, U11. change (bv_eqb 1%bv 0%bv) with false in U1. change (bv_eqb 2%bv 0%bv) with false in U2.
      change (bv_eqb 10%bv 0%bv) with false in U10. change (bv_eqb 11%bv 0%bv) with false in U11. cbv iota in U1, U2, U10, U11.
      apply (lz_renorm L S Zr msF5 mo5 R5 _ M5 _ KX OK5 RS5). intros msFm OKm RSm HSm.
      apply (lz_evt L S Zr (rip_post (reg_get R5 1) (reg_get R5 2) (reg_get R5 3) (reg_get R5 4) (reg_get R5 6) (reg_get R5 7)
                       (reg_get R5 8) (reg_get R5 9) (reg_get R5 18) (reg_get R5 19) (reg_get R5 20) (reg_get R5 21)
                       (reg_get R5 22) (reg_get R5 23) (reg_get R5 24) (reg_get R5 25) (reg_get R5 26) (reg_get R5 27)
                       (reg_get R5 28) (reg_get R5 29) (reg_get R5 30) (reg_get R5 31) bvmap_empty (Z_to_bv 32 0)
                       (bv_unsigned sp - FP_FR) M5) msFm mo5 KX OKm).
      { rewrite RSm. unfold mkR_of. change (Z_to_bv 64 ARIP) with (Z_to_bv 64 rip_entry).
        apply rip_body_w.
        - exact INV5.
        - exact AC5.
        - rewrite U10, U11. apply accessible_of_sh0; [| unfold AHI_LO; lia | unfold AAPP_HI; lia | lia].
          intros a Ha. apply SH5. replace (bv_unsigned pp + (P + 1) - 1) with (bv_unsigned pp + P) in Ha by lia. exact Ha.
        - rewrite U11. lia.
        - rewrite U10, U11. right. unfold AHI_LO, AAPP_HI. lia.
        - rewrite U2. exact (proj1 (stk_split asegs M5 _ (bv_unsigned sp - 2352) _ ST5 ltac:(unfold FP_FR; lia))).
        - rewrite U2. unfold RIP_STACK, FP_FR. lia.
        - unfold AHI_LO, FP_FR. lia. }
      clear OKm RSm. intros msF6 mo6 OK6 SB6 HS6 HP6.
      destruct HP6 as (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m6 & RS6 & MU6 & WM6 & INV6 & ST6 & AC6).
      assert (RP : ret_pc (reg_get R5 1) = Z_to_bv 64 ARIP_RET) by (rewrite U1; unfold ARIP_RET; apply ret_pc_even; [lia | reflexivity]).
      rewrite RP in RS6. clear RP. rewrite U2 in MU6, ST6.
      lazymatch type of RS6 with _ = MS ?Rx _ ?pcx _ _ _ ?romx =>
        change (restrict L S msF6 = mkst Rx pcx m6 romx) in RS6; set (R6 := Rx) in RS6 end.
      assert (G56 : mem_grows M5 m6).
      { eapply (mem_grows_of_stk M5 m6 _ _ (bv_unsigned sp - FP_FR) (bv_unsigned sp - 2352) MU6 ST6); unfold FP_FR; lia. }
      assert (F56 : frame_mod M5 m6 (fp_regions_w sp)) by (eapply fp_frame_mod_of_munch; [exact MU6 | exact G56 | unfold FP_FR; lia | lia | unfold FP_FR; lia]).
      assert (F06 : frame_mod mem m6 (fp_regions_w sp)) by (eapply frame_mod_trans_same; [exact F05 | exact F56]).
      pose proof (know_cut_sound RSEGS (ENV vals) M5 m6 0 (-2432) (-2352) 0x100000000 fp_kn3s'
                    ltac:(unfold win_ok; cbn [ev ENV]; rewrite P0; lia)
                    ltac:(intros x Hx; apply MU6; cbn [outside]; cbn [ev ENV] in Hx; rewrite P0 in Hx; split; [lia | exact I])
                    G56 HK) as HK6.
      change (kn_cut 0 (-2432) (-2352) 0x100000000 fp_kn3s') with fp_kn4se in HK6. clear HK.
      pose proof (env_app_know RSEGS vals (junk_vals R6) (blobs_ev []) m6 fp_kn4se ltac:(rewrite HL; vm_compute; reflexivity) HK6) as HK6'.
      clear HK6. change (Env (vals_ev (vals ++ junk_vals R6)) (blobs_ev [])) with (ENV (vals ++ junk_vals R6)) in HK6'.
      fp_regs_after_rip HR vals HL R6 fp_sr4s HR6. clear HR.
      set (vals1 := vals ++ junk_vals R6) in *.
      assert (HL1 : length vals1 = 66%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (QV1 : forall i, (i < 34)%nat -> vals_ev vals1 i = vals_ev vals i).
      { intros i Hi. subst vals1. rewrite vals_ev_app_l by (rewrite HL; lia). reflexivity. }
      assert (Q0 : vals_ev vals1 0 = sp) by (rewrite QV1 by lia; exact P0).
      assert (Q1 : vals_ev vals1 1 = Z_to_bv 64 P) by (rewrite QV1 by lia; exact P1).
      assert (Q14 : vals_ev vals1 14 = pp) by (rewrite QV1 by lia; exact P14).
      clearbody vals1. clear U1 U2 U10 U11.
      pose proof (fp_regions_flat vals1 sp Q0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF1.
      pose proof (fp_regions_denot vals1 sp Q0 ltac:(unfold ASP_LO; lia)) as RD1.

      fp_block fp_r4s fp_c4s CC4s (SCR [false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] [] []) ARIP_RET fp_sr4s fp_kn4se 66%nat (ENV vals1) m6 R6 msF6 mo6 HR6 HK6'
               ltac:(rewrite SC4s; scs_by vals1 m6 Q0 Q14 Q1) OK6 RS6.
      clear HR6 HK6' RS6. intros R7 M7 msF7 mo7 HR HK EQ7 LF7 OK7 SB7 HS7 RS7.
      pose proof (log_covered_frame (ENV vals1) m6 fp_regions _ fp_cov4s RF1 LF7) as F7. rewrite <- EQ7, RD1 in F7.
      change (s_regs (fst (fst fp_r4s))) with fp_sr4s' in HR. rewrite PC4s in RS7.
      pose proof (know_repack vals1 M7 _ sp Q0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia) HK RP4s) as HK'. clear HK.
      change (repack (fst (fst fp_c4s))) with fp_kn5s in HK'.

      fp_block fp_r5s fp_c5s CC5s scr0 ARET_MEMSET fp_sr4s' fp_kn5s 66%nat (ENV vals1) M7 R7 msF7 mo7 HR HK'
               ltac:(rewrite SC5s; constructor) OK7 RS7.
      clear HR HK' RS7. intros R8 M8 msF8 mo8 HR HK EQ8 LF8 OK8 SB8 HS8 RS8.
      pose proof (log_covered_frame (ENV vals1) M7 fp_regions _ fp_cov5s RF1 LF8) as F8. rewrite <- EQ8, RD1 in F8.
      change (s_regs (fst (fst fp_r5s))) with fp_srFs in HR. change (fst (fst fp_c5s)) with fp_knFs in HK. rewrite PC5s in RS8.
      apply (POST vals1 R8 M8 msF8 mo8 fp_srFs fp_knFs QV1 HR HK ltac:(right; split; reflexivity)); try assumption.
      + eapply frame_mod_trans_same; [exact F06|]. eapply frame_mod_trans_same; [exact F7 | exact F8].
      + eapply same_but_materialized_trans; [exact SB1|]. eapply same_but_materialized_trans; [exact SB2|].
        eapply same_but_materialized_trans; [exact SB3|]. eapply same_but_materialized_trans; [exact SB4|].
        eapply same_but_materialized_trans; [exact SB5|]. eapply same_but_materialized_trans; [exact SB6|].
        eapply same_but_materialized_trans; [exact SB7 | exact SB8].
      + eapply hid_same_trans; [exact HS1|]. eapply hid_same_trans; [exact HS2|]. eapply hid_same_trans; [exact HS3|].
        eapply hid_same_trans; [exact HSn|]. eapply hid_same_trans; [exact HS4|]. eapply hid_same_trans; [exact HS5|].
        eapply hid_same_trans; [exact HSm|]. eapply hid_same_trans; [exact HS6|]. eapply hid_same_trans; [exact HS7 | exact HS8].
  Qed.
End Plain.
