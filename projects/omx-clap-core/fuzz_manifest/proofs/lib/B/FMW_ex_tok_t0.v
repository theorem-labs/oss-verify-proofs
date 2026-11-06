(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 259 of its 305 lines of code are new or changed and 221 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_e.v, with its numbers changed; 225 of its 286 lines of code are new or changed and 244 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_lha.v; 151 of its 203 lines of code are new or changed and 234 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_n.v, with its module paths, module names, addresses and numbers changed; 105 of its 198 lines of code are new or changed and 110 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_ex_tok_n.v, with its numbers changed; 477 of its 532 lines of code are new or changed and 143 lines of the source are left out. *)
(* G4 IMAGE B: tk_seg_T0 (lib/B/FMW_ex_tok_base.v) for fm.asan-ubsan's expected: EX_T 0x816dc .. TK_LH 0x81730
   (listing lines 294-314, fuzz_manifest.c:100-103): ll = strlen (local), len = strlen (text), the loop's first test
   len >= ll + nl + 1, the setup (F+0x10 = ll + nl + 1, F+0x50 = len, a6 = text, s8 = 0, s2 = ll + 1 + nl,
   F+8 = F+0 = text + 1 + nl + ll, F+0x18 = ll, s6 = text + nl, s10 = ~text). The test failing leaves through
   0x8166c .. 0x816a0 (a7, t0, t1 re-made, s7 = close + 1, s5 = text + s7, the guard 0x816a0) to EX_L at close + 1
   (token false). Twin of image A's lib/A/FMW_ex_tok_t0.v (06d82004dc3), which proves its own bounds (it needs no
   FMW_ex_decl_base); the walk is cut after each runtime call:
     EX_T  0x816dc: a0 = local (F+0x20), strlen;                 -> TK_A1
     TK_A1 0x816e4: s10 = ll, s8 = a0 = text (F+0x78), strlen;    -> TK_A2
     TK_A2 0x816f4: a0 = len, the test, the setup or exit       -> TK_LH (j = 0) / EX_L.
   UBSan guard refuted: 0x816a0 (B5 table #40, bgeu ~text, close + 1 not taken -> trap 0x8194c). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_tok_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the cuts after the two strlen calls ---- *)
Definition TK_A1 : Z := 0x816e4.
Definition TK_A2 : Z := 0x816f4.

(* ---- the symbolic states: every register its own atom, atom 2 = sp = F ---- *)
Definition T0_AF2 : nat * afact := (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4).
(* EX_T: F+0x20 = local (extra atom 32) *)
Definition t0_frameA : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x20 0x28 0x20 0x20 [YP09.mkChunk 0x20 (CVal 8 (SOff 32 0))].
Definition ss_TA : sstate := mkSS EX_T sr_atoms [t0_frameA] None (mkFacts [T0_AF2] [] []).
(* TK_A1: F+0x78 = text (extra atom 32) *)
Definition t0_frameB : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x78 0x80 0x78 0x78 [YP09.mkChunk 0x78 (CVal 8 (SOff 32 0))].
Definition ss_TB : sstate := mkSS TK_A1 sr_atoms [t0_frameB] None (mkFacts [T0_AF2] [] []).
(* TK_A2: [F, F + 0x20) writable; F+0x40 = close = text + c (s8's atom 24 plus extra atom 32 = c, so that the exit's
   `sub s7, a1, a6` with a6 = s8 normalizes to atom 32), F+0x70 = the mask, F+0x80 = ~text (extra atom 33);
   [F + 0x50, F + 0x58) writable *)
Definition t0_frameC1 : YP09.region := YP09.mkRegion (Some 2%nat) 0 0x20 0 0x20 [].
Definition t0_frameC2 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x40 0x88 0x50 0x58
    [YP09.mkChunk 0x40 (CVal 8 (SAlu ALU_ADD (SOff 24 0) (SOff 32 0))); YP09.mkChunk 0x70 (CVal 8 (SLit EX_MASK1));
     YP09.mkChunk 0x80 (CVal 8 (SOff 33 0))].
Definition ss_TC : sstate := mkSS TK_A2 sr_atoms [t0_frameC1; t0_frameC2] None (mkFacts [T0_AF2] [] []).

(* a register a runtime call keeps (callee-saved), which the state before the call holds as an atom *)
Ltac t0_cs HP HS EE :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let q := eval vm_compute in (bv_unsigned r) in
    lazymatch type of HP with aregs_preserved ?rT _ =>
      transitivity (getr rT r); [exact (HP q ltac:(unfold acallee_saved; lia)) |] end;
    let Q := fresh "Q" in rreg HS r Q; rewrite Q; apply EE; reflexivity end.
(* awr_ok for frame regions at atom 2 = F = journal sp0 - 240 (G3 FMW_rd_c8.v c8_awr) *)
Ltac t0_awr U2 :=
  lazymatch goal with
  | |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own)
  | |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc ly own)
  end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -240);
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite U2; unfold cx_F; lia
      | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the invariants of the three cuts ---- *)
(* memory: the scan's context at the declaration, ex_com, the slots (declared = d + 1), local and close *)
Definition t0_mem (cx : ecx) (p : tkp) ly3 S3 (W3 : world tfibsegs) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  tk_ctx B cx p /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 (S (tk_d p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x20) 8 (cx_u cx + Z.of_nat (tk_nl2 p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x40) 8 (cx_t cx + Z.of_nat (tk_close p)).
(* registers (callee-saved): s0 = -1, s3 = 5, s11 = ' ', s7 = 1, s4 = text + name, s5 = nl, s2 = 1 + nl,
   s6 = s1 = text + 1 + nl *)
Definition t0_regs (cx : ecx) (p : tkp) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 8 = w64 (2 ^ 64 - 1) /\ getr regs3 19 = w64 5 /\ getr regs3 27 = w64 32 /\ getr regs3 23 = w64 1 /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat (tk_name p)) /\ getr regs3 21 = w64 (Z.of_nat (tk_nl p)) /\
  getr regs3 18 = w64 (1 + Z.of_nat (tk_nl p)) /\ getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat (tk_nl p)) /\
  getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat (tk_nl p)).
(* TK_A1: a0 = ll *)
Definition t0_at_B (cx : ecx) (p : tkp) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ t0_regs cx p regs3 /\ getr regs3 10 = w64 (Z.of_nat (tk_ll cx p)).
(* TK_A2: s10 = ll, s8 = text, a0 = len *)
Definition t0_at_C (cx : ecx) (p : tkp) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ t0_regs cx p regs3 /\ getr regs3 26 = w64 (Z.of_nat (tk_ll cx p)) /\
  getr regs3 24 = w64 (cx_t cx) /\ getr regs3 10 = w64 (Z.of_nat (length (cx_tb cx))).

(* ---- kit ---- *)
Lemma t0_cfg : forall (W : world tfibsegs) pc regs mem md Q,
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

Lemma t0_u64s : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

(* memory kept everywhere but the stack below F and B's setup windows [F, F + 0x20) and [F + 0x50, F + 0x58):
   below alloc_ceiling, [F + 0x20, F + 0x50) and from F + 0x58 up *)
Definition t0_keep (W : world tfibsegs) (m m' : word -> option byte) (F : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ F + 0x20 <= a < F + 0x50 \/ F + 0x58 <= a) ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

Lemma t0_keep_frame : forall E rs (W : world tfibsegs) mem0 m0 m1 F,
  frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) -> t0_keep W mem0 m0 F -> alloc_ceiling <= F ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/
    (F <= base_val E (YP09.r_base r) + YP09.r_wlo r /\ base_val E (YP09.r_base r) + YP09.r_whi r <= F + 0x20) \/
    (F + 0x50 <= base_val E (YP09.r_base r) + YP09.r_wlo r /\
     base_val E (YP09.r_base r) + YP09.r_whi r <= F + 0x58)) rs ->
  t0_keep W mem0 m1 F.
Proof.
  intros E rs W mem0 m0 m1 F HF HK HFa Hrs a Ha Hin.
  rewrite (fw_aview_frame tfibsegs E rs (w_H W) m0 m1 HF a Ha); [exact (HK a Ha Hin)|].
  intros (r & Hr & Hw). rewrite Forall_forall in Hrs. destruct (Hrs r Hr) as [X|[X|X]]; lia.
Qed.

Lemma t0_val_keep : forall W m m' F a v, t0_keep W m m' F -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (a + 8 <= alloc_ceiling \/ (F + 0x20 <= a /\ a + 8 <= F + 0x50) \/ F + 0x58 <= a) ->
  val_mem tfibsegs (rdW W m) a 8 v -> val_mem tfibsegs (rdW W m') a 8 v.
Proof.
  intros W m m' F a v HK H0 H1 Hw Hv. apply (tk_val_move W m m' a 8 v); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK; lia.
Qed.

(* t0_mem across a step that keeps t0_keep (a runtime call at sp = F, or B's setup run) *)
Lemma t0_mem_move : forall cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  t0_keep W3 mem3 mem4 (cx_F cx) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  t0_mem cx p ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HX & HC & HSL & V20 & V40) HJ4 HK Q2 Q3 Q4 Q25.
  pose proof HX as (HB & _).
  pose proof (tk_bounds B cx HB) as (HFm & HFlo & HFhi & HF46 & _). pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 240 + 8224) by reflexivity.
  assert (KL : fw_low tfibsegs (w_H W3) mem3 mem4) by (intros a Ha; apply HK; lia).
  destruct HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  destruct HSL as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  split; [exact HX|]. split.
  { split; [exact HJ4|]. split; [exact Hbl|].
    split; [exact (fw_glob_low tfibsegs W3 mem3 mem4 _ _ _ _ KL HGL)|].
    split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
    split; [rewrite Q25; exact R25|].
    split.
    { unfold ex_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hs.
      assert (Ho : 136 <= fst s <= 232)
        by (cbv [EX_SAVED In] in Hs; repeat (destruct Hs as [<-|Hs]; [cbn [fst]; lia|]); destruct Hs).
      apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact (HSV s Hs)]. }
    split; [exact (fw_rodata_low tfibsegs B _ mem3 mem4 fmw_segs_low KL HRO)|].
    split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Ct)|].
    split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Cu)|].
    split; [exact Kt | exact Ku]. }
  split.
  { unfold ex_slots. cbv zeta.
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S1]|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S2]|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S3']|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S4]|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S5]|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S6]|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S7]|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S8]|].
    split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S9]|].
    apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact S10]. }
  split; [apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact V20]|].
  apply (t0_val_keep W3 mem3 mem4 (cx_F cx) _ _ HK); [lia | lia | lia | exact V40].
Qed.

(* the run's frame with B's setup windows kept: compose with the run's frame_of *)
Ltac t0_avw U2 :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    lazymatch goal with AV : t0_keep ?W ?mem0 m0 ?F |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : t0_keep W mem0 m1 F)
        by (apply (t0_keep_frame Ex rs W mem0 m0 m1 F HFr AV); [lia|];
            lazymatch goal with |- Forall _ ?rs' => let v := eval vm_compute in rs' in change rs' with v end;
            repeat apply Forall_cons; try apply Forall_nil;
            cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val ew ewset Nat.eqb];
            first [left; lia | right; left; rewrite U2; lia | right; right; rewrite U2; lia]);
      clear AV; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
(* a field of the walk's final frame region R (based at atom 2 = F): its chunk at od, read back *)
Ltac t0_field HR U2 od :=
  eapply (fw_field tfibsegs _ _ 2 _ _ _ _ _ _ od 8%N _ _ HR U2);
  [ cbn [In]; repeat (first [left; reflexivity | right])
  | apply fw_sv_U; tk_lin_goal
  | cbn; lia
  | cbn; lia ].

Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.

(* ---- TK_A2 0x816f4: len < ll + nl + 1 -> EX_L at close + 1; else the setup to TK_LH at j = 0 ---- *)
Lemma t0_C : forall cx p ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx (tk_i p) -> tk_k B cx TK_LH (tk_at_LH B cx p 0) ->
  t0_at_C cx p ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs TK_A2 regs3 mem3 md3) (ex_post B cx).
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 HLf HLH
    ((HX & HC & HSL & V20 & V40) & (R8 & R19 & R27 & R23 & R20 & R21 & R18 & R22 & R9) & R26 & R24 & R10).
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HX as (HB & _).
  pose proof (tk_bounds B cx HB) as (HFm & HFlo & HFhi & HF46 & Ht4 & Htc & Hu4 & Huc & Hub).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 240 + 8224) by reflexivity.
  assert (Hll : (tk_ll cx p <= 255)%nat) by (unfold tk_ll; lia).
  pose proof HC as (HJ & _ & _ & R2 & R3 & R4 & R25 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof HSL as (_ & _ & _ & _ & _ & _ & _ & S8 & _ & S10).
  set (ex := [w64 (Z.of_nat (tk_close p)); w64 (2 ^ 64 - 1 - cx_t cx)]).
  set (E := Ereg regs3 ex).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = w64 (Z.of_nat (tk_close p))) by exact (ew_Ereg_extra regs3 ex 0).
  assert (E33 : ew E 33 = w64 (2 ^ 64 - 1 - cx_t cx)) by exact (ew_Ereg_extra regs3 ex 1).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply t0_u64s; lia).
  assert (U9 : bv_unsigned (ew E 9) = cx_t cx + 1 + Z.of_nat (tk_nl p))
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply t0_u64s; lia).
  assert (U10 : bv_unsigned (ew E 10) = Z.of_nat (length (cx_tb cx)))
    by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply t0_u64s; lia).
  assert (U18 : bv_unsigned (ew E 18) = 1 + Z.of_nat (tk_nl p))
    by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply t0_u64s; lia).
  assert (U21 : bv_unsigned (ew E 21) = Z.of_nat (tk_nl p))
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply t0_u64s; lia).
  assert (U22 : bv_unsigned (ew E 22) = cx_t cx + 1 + Z.of_nat (tk_nl p))
    by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply t0_u64s; lia).
  assert (U24 : bv_unsigned (ew E 24) = cx_t cx)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply t0_u64s; lia).
  assert (U26 : bv_unsigned (ew E 26) = Z.of_nat (tk_ll cx p))
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply t0_u64s; lia).
  assert (U32 : bv_unsigned (ew E 32) = Z.of_nat (tk_close p)) by (rewrite E32; apply t0_u64s; lia).
  assert (U33 : bv_unsigned (ew E 33) = 2 ^ 64 - 1 - cx_t cx) by (rewrite E33; apply t0_u64s; lia).
  assert (HS : st_ok tfibsegs E ss_TC (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_A2) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_TC. apply entry_st_ok_full; change (Ereg regs3 ex) with E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, t0_frameC1, t0_frameC2;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U2.
      + split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable tfibsegs); apply Hpres; unfold cx_F, cx_sp in *; lia|].
        apply Forall_nil.
      + split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable tfibsegs); apply Hpres; unfold cx_F, cx_sp in *; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x40 8 (SAlu ALU_ADD (SOff 24 0) (SOff 32 0))
            (cx_t cx + Z.of_nat (tk_close p))); [| cbn; lia | cbn; lia | exact V40].
          rewrite denot_lit_U, U_add_off_atom by (rewrite ?U24, ?U32; unfold M64; lia).
          rewrite U24, U32. f_equal; lia.
        * apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x70 8 (SLit EX_MASK1) EX_MASK1);
            [reflexivity | unfold EX_MASK1; cbn; lia | cbn; lia | exact S8].
        * apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x80 8 (SOff 33 0) (2 ^ 64 - 1 - cx_t cx));
            [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact S10].
    - apply pairwise_disjoint_of_extents. unfold t0_frameC1, t0_frameC2, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok T0_AF2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2. change (2 ^ 4) with 16. repeat split; lia. }
  clearbody E.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 TK_A2) mem3 (seg_rom tfibsegs))))) by constructor.
  assert (AV : t0_keep W3 mem3 mem3 (cx_F cx)) by (intros a _ _; reflexivity).
  unfold cfg_at. change (w64 TK_A2) with (Z_to_bv 64 TK_A2).
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 TK_A2) mem3 (seg_rom tfibsegs))) in HJ.
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { t0_awr U2. }
  t0_avw U2.
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  { (* len < ll + nl + 1: the token is absent; out through 0x8166c .. 0x816a0 to EX_L at close + 1 *)
    assert (Hlt : (length (cx_tb cx) < 0 + tk_nl p + 1 + tk_ll cx p)%nat).
    { rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. tk_lin_in Hc. tk_vals_in Hc. lia. }
    clear Hc.
    aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
    { t0_awr U2. }
    t0_avw U2.
    (* the guard 0x816a0: bgeu ~text, close + 1 -> EX_L; its not-taken arm is the trap *)
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    2: { tk_kill Hc. }
    clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_L.
    { t0_awr U2. }
    t0_avw U2. tk_mk HS.
    assert (HTK : ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = false)
      by (apply (tk_none_false B cx p 0 HX); [intros j' Hj'; lia | lia]).
    pose proof (tk_scan_next B cx p HX HTK) as (Hic & Hsc).
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
      eassert (HM' : t0_mem cx p ly3 S3 W3 (ms_regs msx) (ms_mem msx) _) end.
    { apply (t0_mem_move cx p ly3 S3 W3 regs3 mem3 md3 _ _ _ (conj HX (conj HC (conj HSL (conj V20 V40)))) HJ AV);
        tk_g HS; apply EE; reflexivity. }
    destruct HM' as (_ & HC' & HSL' & _).
    apply (HLf (S (tk_close p)) (S (tk_d p)) (pred (tk_f p)) ly3 S3 W3 _ _ _ Hic).
    split; [exact HB|]. split; [exact HC'|]. split; [exact HSL'|].
    split.
    { unfold ex_sregs.
      split; [tk_g HS; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
      split; [tk_g HS; rewrite (EE 27%nat 27%bv eq_refl); exact R27|].
      tk_g HS; rewrite (EE 8%nat 8%bv eq_refl); exact R8. }
    split.
    { unfold ex_cregs.
      split; [tk_g HS; rewrite (EE 24%nat 24%bv eq_refl); exact R24|].
      split; [tk_g HS; reflexivity|].
      split; [tk_g HS; reflexivity|].
      tk_g HS; reflexivity. }
    split; [exact Hsc|].
    split; tk_Ug HS. }
  { (* len >= ll + nl + 1: the setup, TK_LH at j = 0 *)
    assert (Hge : (0 + tk_nl p + 1 + tk_ll cx p <= length (cx_tb cx))%nat).
    { rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc. tk_lin_in Hc. tk_vals_in Hc. lia. }
    clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_LH.
    { t0_awr U2. }
    t0_avw U2.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msL end.
    lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?H ?msX) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (fw_region_nth tfibsegs Ex ssx (restrict H msX) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
      let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (fw_region_nth tfibsegs Ex ssx (restrict H msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
      cbn [ms_mem restrict] in HR0, HR1 end.
    assert (W0 : val_mem tfibsegs (rdW W3 (ms_mem msL)) (cx_F cx + 0)
      (N.to_nat 8) (cx_t cx + 1 + Z.of_nat (tk_nl p) + Z.of_nat (tk_ll cx p))) by t0_field HR0 U2 0.
    assert (W8 : val_mem tfibsegs (rdW W3 (ms_mem msL)) (cx_F cx + 8)
      (N.to_nat 8) (cx_t cx + 1 + Z.of_nat (tk_nl p) + Z.of_nat (tk_ll cx p))) by t0_field HR0 U2 8.
    assert (W10 : val_mem tfibsegs (rdW W3 (ms_mem msL)) (cx_F cx + 0x10)
      (N.to_nat 8) (Z.of_nat (tk_ll cx p) + 1 + Z.of_nat (tk_nl p))) by t0_field HR0 U2 0x10.
    assert (W18 : val_mem tfibsegs (rdW W3 (ms_mem msL)) (cx_F cx + 0x18)
      (N.to_nat 8) (Z.of_nat (tk_ll cx p))) by t0_field HR0 U2 0x18.
    assert (W50 : val_mem tfibsegs (rdW W3 (ms_mem msL)) (cx_F cx + 0x50)
      (N.to_nat 8) (Z.of_nat (length (cx_tb cx)))) by t0_field HR1 U2 0x50.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in W0, W8, W10, W18, W50. rewrite Z.add_0_r in W0.
    clear HR0 HR1.
    tk_mk HS.
    apply (t0_cfg W3 TK_LH).
    apply (HLH ly3 S3 W3 _ _ _).
    eassert (HM' : t0_mem cx p ly3 S3 W3 (ms_regs msL) (ms_mem msL) _).
    { apply (t0_mem_move cx p ly3 S3 W3 regs3 mem3 md3 _ _ _ (conj HX (conj HC (conj HSL (conj V20 V40)))) HJ AV);
        tk_g HS; apply EE; reflexivity. }
    destruct HM' as (_ & HC' & HSL' & V20' & V40').
    split.
    { split; [exact HX|]. split; [exact HC'|]. split; [exact HSL'|]. split; [exact V20'|]. split; [exact V40'|].
      split; [exact W10|]. split; [exact W50|]. split; [exact W8|]. split; [exact W18 | exact W0]. }
    split.
    { unfold tk_regs.
      split; [tk_g HS; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
      split; [tk_g HS; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
      split; [tk_g HS; rewrite (EE 27%nat 27%bv eq_refl); exact R27|].
      split; [tk_g HS; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
      split; [tk_g HS; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
      split; [tk_g HS; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
      split; [tk_Ug HS|].
      split; [tk_Ug HS|].
      tk_g HS; rewrite (EE 24%nat 24%bv eq_refl); exact R24. }
    split.
    { unfold tk_jr, tk_nt. split; [tk_g HS; reflexivity | tk_Ug HS]. }
    split; [unfold tk_bound; lia|].
    intros j' Hj'. lia. }
Qed.

(* ---- TK_A1 0x816e4: s10 = ll, s8 = a0 = text (F+0x78), strlen (text) -> TK_A2 ---- *)
Lemma t0_B : forall cx p ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx (tk_i p) -> tk_k B cx TK_LH (tk_at_LH B cx p 0) ->
  t0_at_B cx p ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs TK_A1 regs3 mem3 md3) (ex_post B cx).
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 HLf HLH (HM & HR & R10).
  pose proof HM as (HX & HC & HSL & V20 & V40).
  pose proof HR as (R8 & R19 & R27 & R23 & R20 & R21 & R18 & R22 & R9).
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof (tk_bounds B cx HB) as (HFm & HFlo & HFhi & HF46 & Ht4 & Htc & Hu4 & Huc & Hub).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 240 + 8224) by reflexivity. assert (FR : STK_RT_STR = 8192) by reflexivity.
  assert (HF : cx_F cx = cx_sp cx - 240) by reflexivity.
  pose proof HC as (HJ & _ & _ & R2 & R3 & R4 & R25 & _ & HRO & Ct & _).
  pose proof HSL as (_ & _ & _ & _ & _ & _ & _ & _ & S9 & _).
  set (ex := [w64 (cx_t cx)]).
  set (E := Ereg regs3 ex).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = w64 (cx_t cx)) by exact (ew_Ereg_extra regs3 ex 0).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply t0_u64s; lia).
  assert (U32 : bv_unsigned (ew E 32) = cx_t cx) by (rewrite E32; apply t0_u64s; lia).
  assert (HS : st_ok tfibsegs E ss_TB (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_A1) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_TB. apply entry_st_ok_full; change (Ereg regs3 ex) with E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, t0_frameB.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x78 8 (SOff 32 0) (cx_t cx));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact S9].
    - cbn. tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok T0_AF2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2. change (2 ^ 4) with 16. repeat split; lia. }
  clearbody E.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 TK_A1) mem3 (seg_rom tfibsegs))))) by constructor.
  unfold cfg_at. change (w64 TK_A1) with (Z_to_bv 64 TK_A1).
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 TK_A1) mem3 (seg_rom tfibsegs))) in HJ.
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha. apply (fw_nowin tfibsegs _ _ _ _ _ HFr); [vm_compute; reflexivity | exact Ha]. }
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  assert (KL : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms)) by (intros a Ha; apply AV; lia).
  rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
  rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply SRr_bind.
  { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strlen STK_RT_STR (fun v => v = Z.of_nat (length (cx_tb cx)))
      W3 (ms_regs ms) (ms_mem ms) STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) []
      ly3 S3 _ 0 (-240) (Z_to_bv 64 0x816f4) HJ).
    - unfold spZ at 1. rewrite Rsp, U2. lia.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - lia.
    - rewrite Rgp, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
    - rewrite Rtp, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
    - exact Rra.
    - vm_compute. reflexivity.
    - intros HPK. apply (STRLEN ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (cx_t cx) (cx_tb cx) HPK).
      + exact (proj1 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL HRO))).
      + rewrite Ra0, E32. reflexivity.
      + exact (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL Ct). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
  apply (t0_cfg W3 TK_A2).
  apply (t0_C cx p ly3 S3 W3 regs2 mem2 md2 HLf HLH).
  assert (K2 : t0_keep W3 mem3 mem2 (cx_F cx)).
  { intros a Ha Hn. rewrite (Hfr2 a Ha) by (rewrite HF in Hn; lia). exact (AV a Ha). }
  split.
  { apply (t0_mem_move cx p ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2 HM HJ2 K2); t0_cs HP2 HS EE. }
  split.
  { split; [transitivity (getr regs3 8); [t0_cs HP2 HS EE | exact R8]|].
    split; [transitivity (getr regs3 19); [t0_cs HP2 HS EE | exact R19]|].
    split; [transitivity (getr regs3 27); [t0_cs HP2 HS EE | exact R27]|].
    split; [transitivity (getr regs3 23); [t0_cs HP2 HS EE | exact R23]|].
    split; [transitivity (getr regs3 20); [t0_cs HP2 HS EE | exact R20]|].
    split; [transitivity (getr regs3 21); [t0_cs HP2 HS EE | exact R21]|].
    split; [transitivity (getr regs3 18); [t0_cs HP2 HS EE | exact R18]|].
    split; [transitivity (getr regs3 22); [t0_cs HP2 HS EE | exact R22]|].
    transitivity (getr regs3 9); [t0_cs HP2 HS EE | exact R9]. }
  split.
  { transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia))|].
    let Q := fresh "Q" in rreg HS (26%bv : bv 5) Q; rewrite Q.
    rewrite (EE 10%nat 10%bv eq_refl). exact R10. }
  split.
  { transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia))|].
    let Q := fresh "Q" in rreg HS (24%bv : bv 5) Q; rewrite Q.
    exact E32. }
  rewrite Hv, Hvl. reflexivity.
Qed.

(* ---- EX_T 0x816dc: a0 = local (F+0x20), strlen (local) -> TK_A1 ---- *)
Lemma t0_A : forall cx p ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx (tk_i p) -> tk_k B cx TK_LH (tk_at_LH B cx p 0) ->
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 -> t0_regs cx p regs3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_T regs3 mem3 md3) (ex_post B cx).
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 HLf HLH HM HR.
  pose proof HM as (HX & HC & HSL & V20 & V40).
  pose proof HR as (R8 & R19 & R27 & R23 & R20 & R21 & R18 & R22 & R9).
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof (tk_bounds B cx HB) as (HFm & HFlo & HFhi & HF46 & Ht4 & Htc & Hu4 & Huc & Hub).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 240 + 8224) by reflexivity. assert (FR : STK_RT_STR = 8192) by reflexivity.
  assert (HF : cx_F cx = cx_sp cx - 240) by reflexivity.
  pose proof HC as (HJ & _ & _ & R2 & R3 & R4 & R25 & _ & HRO & _ & Cu & _).
  set (ex := [w64 (cx_u cx + Z.of_nat (tk_nl2 p))]).
  set (E := Ereg regs3 ex).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = w64 (cx_u cx + Z.of_nat (tk_nl2 p))) by exact (ew_Ereg_extra regs3 ex 0).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply t0_u64s; lia).
  assert (U32 : bv_unsigned (ew E 32) = cx_u cx + Z.of_nat (tk_nl2 p)) by (rewrite E32; apply t0_u64s; lia).
  assert (HS : st_ok tfibsegs E ss_TA (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_T) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_TA. apply entry_st_ok_full; change (Ereg regs3 ex) with E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, t0_frameA.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x20 8 (SOff 32 0) (cx_u cx + Z.of_nat (tk_nl2 p)));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact V20].
    - cbn. tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok T0_AF2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2. change (2 ^ 4) with 16. repeat split; lia. }
  clearbody E.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_T) mem3 (seg_rom tfibsegs))))) by constructor.
  unfold cfg_at. change (w64 EX_T) with (Z_to_bv 64 EX_T).
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_T) mem3 (seg_rom tfibsegs))) in HJ.
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha. apply (fw_nowin tfibsegs _ _ _ _ _ HFr); [vm_compute; reflexivity | exact Ha]. }
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  assert (KL : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms)) by (intros a Ha; apply AV; lia).
  rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
  rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply SRr_bind.
  { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strlen STK_RT_STR
      (fun v => v = Z.of_nat (length (skipn (tk_nl2 p) (cx_ub cx))))
      W3 (ms_regs ms) (ms_mem ms) STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) []
      ly3 S3 _ 0 (-240) (Z_to_bv 64 0x816e4) HJ).
    - unfold spZ at 1. rewrite Rsp, U2. lia.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - lia.
    - rewrite Rgp, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
    - rewrite Rtp, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
    - exact Rra.
    - vm_compute. reflexivity.
    - intros HPK. apply (STRLEN ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (cx_u cx + Z.of_nat (tk_nl2 p))
        (skipn (tk_nl2 p) (cx_ub cx)) HPK).
      + exact (proj1 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL HRO))).
      + rewrite Ra0, E32. reflexivity.
      + apply tk_cstr_suffix; [lia | exact (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL Cu)]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
  apply (t0_cfg W3 TK_A1).
  apply (t0_B cx p ly3 S3 W3 regs2 mem2 md2 HLf HLH).
  assert (K2 : t0_keep W3 mem3 mem2 (cx_F cx)).
  { intros a Ha Hn. rewrite (Hfr2 a Ha) by (rewrite HF in Hn; lia). exact (AV a Ha). }
  split.
  { apply (t0_mem_move cx p ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2 HM HJ2 K2); t0_cs HP2 HS EE. }
  split.
  { split; [transitivity (getr regs3 8); [t0_cs HP2 HS EE | exact R8]|].
    split; [transitivity (getr regs3 19); [t0_cs HP2 HS EE | exact R19]|].
    split; [transitivity (getr regs3 27); [t0_cs HP2 HS EE | exact R27]|].
    split; [transitivity (getr regs3 23); [t0_cs HP2 HS EE | exact R23]|].
    split; [transitivity (getr regs3 20); [t0_cs HP2 HS EE | exact R20]|].
    split; [transitivity (getr regs3 21); [t0_cs HP2 HS EE | exact R21]|].
    split; [transitivity (getr regs3 18); [t0_cs HP2 HS EE | exact R18]|].
    split; [transitivity (getr regs3 22); [t0_cs HP2 HS EE | exact R22]|].
    transitivity (getr regs3 9); [t0_cs HP2 HS EE | exact R9]. }
  rewrite Hv, Hvl, length_skipn. reflexivity.
Qed.

Theorem tk_seg_T0_holds : tk_seg_T0 B.
Proof.
  intros cx i d f name nl ns nl2 close HLf HLH ly3 S3 W3 regs3 mem3 md3 HT.
  destruct HT as (HB & HC & HSL & (R19 & R27 & R8) & Hsc & Hit & Hsd & Hdc & Hm & V20 & V40 &
    R23 & R20 & R21 & R18 & R22 & R9 & _).
  apply (t0_A cx (mkTKP i d f name nl ns nl2 close) ly3 S3 W3 regs3 mem3 md3 HLf HLH).
  - exact (conj (conj HB (conj Hsc (conj Hit (conj Hsd (conj Hdc Hm))))) (conj HC (conj HSL (conj V20 V40)))).
  - exact (conj R8 (conj R19 (conj R27 (conj R23 (conj R20 (conj R21 (conj R18 (conj R22 R9)))))))).
Qed.
End c.

About tk_seg_T0_holds.
Print Assumptions tk_seg_T0_holds.
