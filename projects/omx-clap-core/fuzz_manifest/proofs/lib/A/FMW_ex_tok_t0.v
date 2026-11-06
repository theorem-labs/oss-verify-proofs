(* G4.ExTok.TokT0: tk_seg_T0 (FMW_ex_tok_base.v:181) for fm.asan's expected: EX_T 0x8152c .. TK_LH 0x81574
   (expected.dis lines 256-273, fuzz_manifest.c:100-103): ll = strlen (local), len = strlen (text), the loop's first
   test len >= ll + nl + 1, the setup (s11 = len, s10 = 0, s8 = ll + 1 + nl, F+0x10 = text + nl,
   F+0 = s1 = text + 1 + nl + ll, s3 = ll). The test failing leaves through 0x814c8 .. 0x814e0 to EX_L at close + 1
   (token false). The walk is cut after each runtime call (as G3's FMW_rd_c8.v, a Theorem Labs lane, does):
     EX_T  0x8152c: a0 = local, strlen;                  -> TK_A1
     TK_A1 0x81534: s10 = ll, a0 = text, strlen;          -> TK_A2
     TK_A2 0x81540: a0 = len, the test, the setup or exit -> TK_LH (j = 0) / EX_L. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_base FMW_ex_tok_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the cuts after the two strlen calls ---- *)
Definition TK_A1 : Z := 0x81534.
Definition TK_A2 : Z := 0x81540.

(* ---- the symbolic states: every register its own atom, atom 2 = sp = F ---- *)
Definition T0_AF2 : nat * afact := (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4).
(* EX_T: F+8 = local (extra atom 32) *)
Definition t0_frameA : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 0x10 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))].
Definition ss_TA : sstate := mkSS EX_T sr_atoms [t0_frameA] None (mkFacts [T0_AF2] [] []).
(* TK_A1: no memory read *)
Definition ss_TB : sstate := mkSS TK_A1 sr_atoms [] None (mkFacts [T0_AF2] [] []).
(* TK_A2: F+8 = local (atom 32), F+0x28 = close (atom 33), F+0x60 = the mask; [F, F + 0x18) writable *)
Definition t0_frameC : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 0x68 0 0x18
    [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 33 0));
     YP09.mkChunk 0x60 (CVal 8 (SLit EX_MASK1))].
Definition ss_TC : sstate := mkSS TK_A2 sr_atoms [t0_frameC] None (mkFacts [T0_AF2] [] []).

(* ---- walk tactics (after FMW_plain.v fw_reg / pl_mk, G3 FMW_rd_c8.v c8_ulin) ---- *)
Ltac t0_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac t0_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac t0_ulin :=
  lazymatch goal with |- U ?E ?v = _ =>
    let r := eval vm_compute in (lin_nf v) in
    lazymatch r with Some (?l, ?c) =>
      rewrite (lin_nf_sound E v l c ltac:(vm_compute; reflexivity)); cbn [lin_denot] end end.
(* a register the state holds as an atom: its entry register *)
Ltac t0_greg HS EE :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let Q := fresh "Q" in rreg HS r Q; rewrite Q; apply EE; reflexivity end.
(* a register a runtime call keeps (callee-saved), which the state before the call holds as an atom *)
Ltac t0_cs HP HS EE :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let q := eval vm_compute in (bv_unsigned r) in
    lazymatch type of HP with aregs_preserved ?rT _ =>
      transitivity (getr rT r); [exact (HP q ltac:(unfold acallee_saved; lia)) |] end;
    let Q := fresh "Q" in rreg HS r Q; rewrite Q; apply EE; reflexivity end.
(* awr_ok for a frame region at atom 2 = F = journal sp0 - 208 (G3 FMW_rd_c8.v c8_awr) *)
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
    | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -208);
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
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 8) 8 (cx_u cx + Z.of_nat (tk_nl2 p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x28) 8 (cx_t cx + Z.of_nat (tk_close p)).
(* registers: s0 = ' ', s2 = 5, s6 = 6, s7 = text, s4 = text + name, s5 = nl, s8 = 1 + nl, s3 = s1 = text + 1 + nl *)
Definition t0_regs (cx : ecx) (p : tkp) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 8 = w64 32 /\ getr regs3 18 = w64 5 /\ getr regs3 22 = w64 6 /\ getr regs3 23 = w64 (cx_t cx) /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat (tk_name p)) /\ getr regs3 21 = w64 (Z.of_nat (tk_nl p)) /\
  getr regs3 24 = w64 (1 + Z.of_nat (tk_nl p)) /\ getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat (tk_nl p)) /\
  getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat (tk_nl p)).
(* TK_A1: a0 = ll *)
Definition t0_at_B (cx : ecx) (p : tkp) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ t0_regs cx p regs3 /\ getr regs3 10 = w64 (Z.of_nat (tk_ll cx p)).
(* TK_A2: s10 = ll, a0 = len *)
Definition t0_at_C (cx : ecx) (p : tkp) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ t0_regs cx p regs3 /\ getr regs3 26 = w64 (Z.of_nat (tk_ll cx p)) /\
  getr regs3 10 = w64 (Z.of_nat (length (cx_tb cx))).

(* ---- kit ---- *)
Lemma t0_cfg : forall (W : world tfibsegs) pc regs mem md Q,
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

Lemma t0_u64s : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma t0_mod_eq : forall x y k, x = y + k * M64 -> 0 <= y < M64 -> x mod M64 = y.
Proof. intros x y k -> Hy. rewrite Z_mod_plus_full. apply Z.mod_small. exact Hy. Qed.

(* the frame and the strings (after FMW_ex_decl_base.v dd_bounds) *)
Lemma t0_bounds : forall cx, ex_base B cx ->
  cx_F cx mod 16 = 0 /\ alloc_ceiling + STK_expected - 208 <= cx_F cx /\ cx_F cx + 208 <= 2 ^ 47 /\
  4096 <= cx_t cx /\ cx_t cx + Z.of_nat (length (cx_tb cx)) + 8 <= alloc_ceiling /\
  4096 <= cx_u cx /\ cx_u cx + Z.of_nat (length (cx_ub cx)) + 8 <= alloc_ceiling /\
  (length (cx_ub cx) <= 255)%nat.
Proof.
  intros cx ((HPRE & _) & _ & _ & _ & Ct & Cu & _ & _ & Hlen & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof Ct as (_ & Ht4 & Htc & _). pose proof Cu as (_ & Hu4 & Huc & _).
  unfold cx_F, cx_sp in *.
  split; [replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia;
          rewrite Z_mod_plus_full; exact Hal16|].
  split; [lia|]. split; [lia|]. split; [exact Ht4|]. split; [exact Htc|]. split; [exact Hu4|].
  split; [exact Huc | exact Hlen].
Qed.

(* memory kept outside a window [lo, hi) *)
Definition t0_kept (W : world tfibsegs) (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

Lemma t0_kept_frame : forall E rs (W : world tfibsegs) mem0 m0 m1 lo hi,
  frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) -> t0_kept W mem0 m0 lo hi ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/
    (lo <= base_val E (YP09.r_base r) + YP09.r_wlo r /\ base_val E (YP09.r_base r) + YP09.r_whi r <= hi)) rs ->
  t0_kept W mem0 m1 lo hi.
Proof.
  intros E rs W mem0 m0 m1 lo hi HF HK Hrs a Ha Hn.
  rewrite (fw_win tfibsegs E rs (w_H W) m0 m1 lo hi HF Hrs a Ha Hn). exact (HK a Ha Hn).
Qed.

Lemma t0_val_kept : forall W m m' lo hi a v, t0_kept W m m' lo hi -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (hi <= a \/ a + 8 <= lo) -> val_mem tfibsegs (rdW W m) a 8 v -> val_mem tfibsegs (rdW W m') a 8 v.
Proof.
  intros W m m' lo hi a v HK H0 H1 Hw Hv. apply (tk_val_move W m m' a 8 v); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK; lia.
Qed.

(* ex_com across a step that writes only [lo, hi), below F + 0x18 and above alloc_ceiling (after FMW_ex_decl_base.v
   dd_com_kept) *)
Lemma t0_com_move : forall cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 lo hi,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  alloc_ceiling <= lo -> hi <= cx_F cx + 0x18 -> t0_kept W3 mem3 mem4 lo hi ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  ex_com B cx ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 lo hi HB HC HJ4 Hlo Hhi HK Q2 Q3 Q4 Q25.
  pose proof (t0_bounds cx HB) as (HFm & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8432) by reflexivity.
  destruct HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  assert (KL : fw_low tfibsegs (w_H W3) mem3 mem4) by (intros a Ha; apply HK; lia).
  split; [exact HJ4|]. split; [exact Hbl|].
  split; [exact (fw_glob_low tfibsegs W3 mem3 mem4 _ _ _ _ KL HGL)|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q25; exact R25|].
  split.
  { unfold ex_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hs.
    assert (Ho : 104 <= fst s <= 200)
      by (cbv [EX_SAVED In] in Hs; repeat (destruct Hs as [<-|Hs]; [cbn [fst]; lia|]); destruct Hs).
    apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact (HSV s Hs)]. }
  split; [exact (fw_rodata_low tfibsegs B _ mem3 mem4 fmw_segs_low KL HRO)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Ct)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Cu)|].
  split; [exact Kt | exact Ku].
Qed.

Lemma t0_slots_move : forall cx W3 mem3 mem4 lo hi d, ex_base B cx -> t0_kept W3 mem3 mem4 lo hi ->
  hi <= cx_F cx + 0x18 -> ex_slots cx W3 mem3 d -> ex_slots cx W3 mem4 d.
Proof.
  intros cx W3 mem3 mem4 lo hi d HB HK Hhi (S18 & S20 & S30 & S38 & S40 & S48 & S50 & S58 & S60).
  pose proof (t0_bounds cx HB) as (HFm & HFlo & HFhi & _). pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8432) by reflexivity.
  unfold ex_slots. cbv zeta.
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S18]|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S20]|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S30]|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S38]|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S40]|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S48]|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S50]|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S58]|].
  apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact S60].
Qed.

(* t0_mem across a runtime call at sp = F (it writes only [lo, hi), hi <= F) *)
Lemma t0_mem_move : forall cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 lo hi,
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  alloc_ceiling <= lo -> hi <= cx_F cx -> t0_kept W3 mem3 mem4 lo hi ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  t0_mem cx p ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 lo hi (HX & HC & HSL & V8 & V28) HJ4 Hlo Hhi HK Q2 Q3 Q4 Q25.
  pose proof HX as (HB & _).
  pose proof (t0_bounds cx HB) as (HFm & HFlo & HFhi & _). pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8432) by reflexivity.
  split; [exact HX|].
  split; [exact (t0_com_move cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 lo hi HB HC HJ4 Hlo ltac:(lia) HK Q2 Q3 Q4 Q25)|].
  split; [exact (t0_slots_move cx W3 mem3 mem4 lo hi _ HB HK ltac:(lia) HSL)|].
  split; [apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact V8]|].
  apply (t0_val_kept W3 mem3 mem4 lo hi _ _ HK); [lia | lia | lia | exact V28].
Qed.

(* the run's frame with window [lo, hi) kept: compose with the run's frame_of *)
Ltac t0_avw U2 :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    lazymatch goal with AV : t0_kept ?W ?mem0 m0 ?lo ?hi |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : t0_kept W mem0 m1 lo hi)
        by (apply (t0_kept_frame Ex rs W mem0 m0 m1 lo hi HFr AV);
            lazymatch goal with |- Forall _ ?rs' => let v := eval vm_compute in rs' in change rs' with v end;
            repeat apply Forall_cons; try apply Forall_nil;
            cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val ew ewset Nat.eqb];
            first [left; lia | right; rewrite U2; lia]);
      clear AV; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.

Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.

(* ---- TK_A2 0x81540: len < ll + nl + 1 -> EX_L at close + 1; else the setup to TK_LH at j = 0 ---- *)
Lemma t0_C : forall cx p ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx (tk_i p) -> tk_k B cx TK_LH (tk_at_LH B cx p 0) ->
  t0_at_C cx p ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs TK_A2 regs3 mem3 md3) (ex_post B cx).
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 HLf HLH
    ((HX & HC & HSL & V8 & V28) & (R8 & R18 & R22 & R23 & R20 & R21 & R24 & R19 & R9) & R26 & R10).
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HX as (HB & _).
  pose proof (t0_bounds cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc & Hub).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity.
  assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
  assert (Hll : (tk_ll cx p <= 255)%nat) by (unfold tk_ll; lia).
  pose proof HC as (HJ & _ & _ & R2 & R3 & R4 & R25 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof HSL as (_ & _ & _ & _ & _ & _ & _ & _ & S60).
  set (ex := [w64 (cx_u cx + Z.of_nat (tk_nl2 p)); w64 (cx_t cx + Z.of_nat (tk_close p))]).
  set (E := Ereg regs3 ex).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = w64 (cx_u cx + Z.of_nat (tk_nl2 p))) by exact (ew_Ereg_extra regs3 ex 0).
  assert (E33 : ew E 33 = w64 (cx_t cx + Z.of_nat (tk_close p))) by exact (ew_Ereg_extra regs3 ex 1).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply t0_u64s; lia).
  assert (U9 : bv_unsigned (ew E 9) = cx_t cx + 1 + Z.of_nat (tk_nl p))
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply t0_u64s; lia).
  assert (U10 : bv_unsigned (ew E 10) = Z.of_nat (length (cx_tb cx)))
    by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply t0_u64s; lia).
  assert (U19 : bv_unsigned (ew E 19) = cx_t cx + 1 + Z.of_nat (tk_nl p))
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply t0_u64s; lia).
  assert (U21 : bv_unsigned (ew E 21) = Z.of_nat (tk_nl p))
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply t0_u64s; lia).
  assert (U23 : bv_unsigned (ew E 23) = cx_t cx)
    by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply t0_u64s; lia).
  assert (U24 : bv_unsigned (ew E 24) = 1 + Z.of_nat (tk_nl p))
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply t0_u64s; lia).
  assert (U26 : bv_unsigned (ew E 26) = Z.of_nat (tk_ll cx p))
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply t0_u64s; lia).
  assert (U32 : bv_unsigned (ew E 32) = cx_u cx + Z.of_nat (tk_nl2 p)) by (rewrite E32; apply t0_u64s; lia).
  assert (U33 : bv_unsigned (ew E 33) = cx_t cx + Z.of_nat (tk_close p)) by (rewrite E33; apply t0_u64s; lia).
  assert (HS : st_ok tfibsegs E ss_TC (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_A2) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_TC. apply entry_st_ok_full; change (Ereg regs3 ex) with E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, t0_frameC.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable tfibsegs); apply Hpres; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (chunk_ok_val tfibsegs E _ (cx_F cx) 8 8 (SOff 32 0) (cx_u cx + Z.of_nat (tk_nl2 p)));
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact V8].
      + apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x28 8 (SOff 33 0) (cx_t cx + Z.of_nat (tk_close p)));
          [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact V28].
      + apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x60 8 (SLit EX_MASK1) EX_MASK1);
          [reflexivity | unfold EX_MASK1; cbn; lia | cbn; lia | exact S60].
    - cbn. tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok T0_AF2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2. change (2 ^ 4) with 16. repeat split; lia. }
  clearbody E.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 TK_A2) mem3 (seg_rom tfibsegs))))) by constructor.
  assert (AV : t0_kept W3 mem3 mem3 (cx_F cx) (cx_F cx + 0x18)) by (intros a _ _; reflexivity).
  unfold cfg_at. change (w64 TK_A2) with (Z_to_bv 64 TK_A2).
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 TK_A2) mem3 (seg_rom tfibsegs))) in HJ.
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { t0_awr U2. }
  t0_avw U2.
  assert (UB : U E (SAlu ALU_ADD (SOff 21 1) (SOff 26 0)) = Z.of_nat (tk_nl p) + 1 + Z.of_nat (tk_ll cx p)).
  { t0_ulin. rewrite ?U21, ?U26. rewrite Z.mod_small by (unfold M64; lia). lia. }
  assert (UA : U E (SOff 10 0) = Z.of_nat (length (cx_tb cx))).
  { rewrite U_SOff, U10, Z.add_0_r. apply zcanon_id. unfold M64. lia. }
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  { (* len < ll + nl + 1: the token is absent; EX_L at close + 1 *)
    rewrite branch_ltu_U, UA, UB in Hc. apply Z.ltb_lt in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_L.
    { t0_awr U2. }
    t0_avw U2. t0_mk HS.
    assert (HTK : ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = false)
      by (apply (tk_none_false B cx p 0 HX); [intros j' Hj'; lia | lia]).
    pose proof (tk_scan_next B cx p HX HTK) as (Hic & Hsc).
    apply (HLf (S (tk_close p)) (S (tk_d p)) (pred (tk_f p)) ly3 S3 W3 _ _ _ Hic).
    split; [exact HB|].
    split.
    { apply (t0_com_move cx ly3 S3 W3 regs3 mem3 md3 _ _ _ (cx_F cx) (cx_F cx + 0x18) HB HC HJ); [lia | lia | exact AV | ..];
        t0_greg HS EE. }
    split; [exact (t0_slots_move cx W3 mem3 _ _ _ _ HB AV ltac:(lia) HSL)|].
    split.
    { split; [t0_reg HS (23%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
      split; [t0_reg HS (22%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
      split; [t0_reg HS (18%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      t0_reg HS (8%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite (EE 8%nat 8%bv eq_refl); exact R8. }
    split; [exact Hsc|].
    split.
    { t0_reg HS (19%bv : bv 5). unfold w64. apply fw_sv_U. t0_ulin. rewrite ?U23, ?U33.
      apply (t0_mod_eq _ _ (cx_t cx)); unfold M64; lia. }
    split; [t0_reg HS (9%bv : bv 5); reflexivity|].
    split; [t0_reg HS (15%bv : bv 5); reflexivity|].
    t0_reg HS (16%bv : bv 5); reflexivity. }
  { (* len >= ll + nl + 1: the setup, TK_LH at j = 0 *)
    rewrite branch_ltu_U, UA, UB in Hc. apply Z.ltb_ge in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_LH.
    { t0_awr U2. }
    t0_avw U2.
    lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?H ?msX) =>
      let r := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (fw_region_nth tfibsegs Ex ssx (restrict H msX) 0 r HS ltac:(vm_compute; reflexivity)) as HR0;
      cbn [ms_mem restrict] in HR0 end.
    pose proof (fw_field tfibsegs E _ 2 (cx_F cx) _ _ _ _ _ 0 8%N (SAlu ALU_ADD (SOff 19 0) (SOff 26 0))
      (cx_t cx + 1 + Z.of_nat (tk_nl p) + Z.of_nat (tk_ll cx p)) HR0 U2 ltac:(cbn; tauto)
      ltac:(apply fw_sv_U; t0_ulin; rewrite ?U19, ?U26; rewrite Z.mod_small by (unfold M64; lia); lia)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
    pose proof (fw_field tfibsegs E _ 2 (cx_F cx) _ _ _ _ _ 0x10 8%N (SAlu ALU_ADD (SOff 21 0) (SOff 23 0))
      (cx_t cx + Z.of_nat (tk_nl p)) HR0 U2 ltac:(cbn; tauto)
      ltac:(apply fw_sv_U; t0_ulin; rewrite ?U21, ?U23; rewrite Z.mod_small by (unfold M64; lia); lia)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V10.
    pose proof (fw_field tfibsegs E _ 2 (cx_F cx) _ _ _ _ _ 8 8%N (SOff 32 0)
      (cx_u cx + Z.of_nat (tk_nl2 p)) HR0 U2 ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V8'.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V10, V8'. rewrite Z.add_0_r in V0. clear HR0.
    t0_mk HS.
    apply (t0_cfg W3 TK_LH).
    apply (HLH ly3 S3 W3 _ _ _).
    split.
    { split; [exact HX|].
      split.
      { apply (t0_com_move cx ly3 S3 W3 regs3 mem3 md3 _ _ _ (cx_F cx) (cx_F cx + 0x18) HB HC HJ);
          [lia | lia | exact AV | ..]; t0_greg HS EE. }
      split; [exact (t0_slots_move cx W3 mem3 _ _ _ _ HB AV ltac:(lia) HSL)|].
      split; [exact V8'|].
      split; [apply (t0_val_kept W3 mem3 _ (cx_F cx) (cx_F cx + 0x18) _ _ AV); [lia | lia | lia | exact V28]|].
      split; [exact V10 | exact V0]. }
    split.
    { split; [t0_reg HS (8%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
      split; [t0_reg HS (18%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      split; [t0_reg HS (22%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
      split; [t0_reg HS (20%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
      split; [t0_reg HS (21%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
      split; [t0_reg HS (24%bv : bv 5); unfold w64; apply fw_sv_U; t0_ulin; rewrite ?U24, ?U26;
              rewrite Z.mod_small by (unfold M64; lia); lia|].
      split; [t0_reg HS (27%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 10%nat 10%bv eq_refl); exact R10|].
      split; [t0_reg HS (19%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
              rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
      t0_reg HS (9%bv : bv 5); unfold w64; apply fw_sv_U; t0_ulin; rewrite ?U9, ?U26;
        rewrite Z.mod_small by (unfold M64; lia); lia. }
    split; [t0_reg HS (23%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
            rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [t0_reg HS (26%bv : bv 5); reflexivity|].
    split; [unfold tk_bound; lia|].
    intros j' Hj'. lia. }
Qed.

(* ---- TK_A1 0x81534: s10 = ll, strlen (text) -> TK_A2 ---- *)
Lemma t0_B : forall cx p ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx (tk_i p) -> tk_k B cx TK_LH (tk_at_LH B cx p 0) ->
  t0_at_B cx p ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs TK_A1 regs3 mem3 md3) (ex_post B cx).
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 HLf HLH (HM & HR & R10).
  pose proof HM as (HX & HC & HSL & V8 & V28).
  pose proof HR as (R8 & R18 & R22 & R23 & R20 & R21 & R24 & R19 & R9).
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof (t0_bounds cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc & Hub).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity. assert (FR : STK_RT_STR = 8192) by reflexivity.
  assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
  pose proof HC as (HJ & _ & _ & R2 & R3 & R4 & R25 & _ & HRO & Ct & _).
  set (E := Ereg regs3 []).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply t0_u64s; lia).
  assert (HS : st_ok tfibsegs E ss_TB (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_A1) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_TB. apply entry_st_ok_full; change (Ereg regs3 []) with E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
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
      ly3 S3 _ 0 (-208) (Z_to_bv 64 0x81540) HJ).
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
      + rewrite Ra0, (EE 23%nat 23%bv eq_refl). exact R23.
      + exact (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL Ct). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
  apply (t0_cfg W3 TK_A2).
  apply (t0_C cx p ly3 S3 W3 regs2 mem2 md2 HLf HLH).
  assert (K2 : t0_kept W3 mem3 mem2 (cx_F cx - STK_RT_STR) (cx_F cx)).
  { intros a Ha Hn. rewrite (Hfr2 a Ha) by (rewrite HF in Hn; lia). exact (AV a Ha). }
  split.
  { apply (t0_mem_move cx p ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2 (cx_F cx - STK_RT_STR) (cx_F cx) HM HJ2);
      [lia | lia | exact K2 | ..];
      t0_cs HP2 HS EE. }
  split.
  { split; [transitivity (getr regs3 8); [t0_cs HP2 HS EE | exact R8]|].
    split; [transitivity (getr regs3 18); [t0_cs HP2 HS EE | exact R18]|].
    split; [transitivity (getr regs3 22); [t0_cs HP2 HS EE | exact R22]|].
    split; [transitivity (getr regs3 23); [t0_cs HP2 HS EE | exact R23]|].
    split; [transitivity (getr regs3 20); [t0_cs HP2 HS EE | exact R20]|].
    split; [transitivity (getr regs3 21); [t0_cs HP2 HS EE | exact R21]|].
    split; [transitivity (getr regs3 24); [t0_cs HP2 HS EE | exact R24]|].
    split; [transitivity (getr regs3 19); [t0_cs HP2 HS EE | exact R19]|].
    transitivity (getr regs3 9); [t0_cs HP2 HS EE | exact R9]. }
  split.
  { transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia))|].
    let Q := fresh "Q" in rreg HS (26%bv : bv 5) Q; rewrite Q.
    rewrite (EE 10%nat 10%bv eq_refl). exact R10. }
  rewrite Hv, Hvl. reflexivity.
Qed.

(* ---- EX_T 0x8152c: a0 = local (F+8), strlen (local) -> TK_A1 ---- *)
Lemma t0_A : forall cx p ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx (tk_i p) -> tk_k B cx TK_LH (tk_at_LH B cx p 0) ->
  t0_mem cx p ly3 S3 W3 regs3 mem3 md3 -> t0_regs cx p regs3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_T regs3 mem3 md3) (ex_post B cx).
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 HLf HLH HM HR.
  pose proof HM as (HX & HC & HSL & V8 & V28).
  pose proof HR as (R8 & R18 & R22 & R23 & R20 & R21 & R24 & R19 & R9).
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof (t0_bounds cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc & Hub).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8432) by reflexivity. assert (FR : STK_RT_STR = 8192) by reflexivity.
  assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
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
      apply (chunk_ok_val tfibsegs E _ (cx_F cx) 8 8 (SOff 32 0) (cx_u cx + Z.of_nat (tk_nl2 p)));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact V8].
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
      ly3 S3 _ 0 (-208) (Z_to_bv 64 0x81534) HJ).
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
  assert (K2 : t0_kept W3 mem3 mem2 (cx_F cx - STK_RT_STR) (cx_F cx)).
  { intros a Ha Hn. rewrite (Hfr2 a Ha) by (rewrite HF in Hn; lia). exact (AV a Ha). }
  split.
  { apply (t0_mem_move cx p ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2 (cx_F cx - STK_RT_STR) (cx_F cx) HM HJ2);
      [lia | lia | exact K2 | ..];
      t0_cs HP2 HS EE. }
  split.
  { split; [transitivity (getr regs3 8); [t0_cs HP2 HS EE | exact R8]|].
    split; [transitivity (getr regs3 18); [t0_cs HP2 HS EE | exact R18]|].
    split; [transitivity (getr regs3 22); [t0_cs HP2 HS EE | exact R22]|].
    split; [transitivity (getr regs3 23); [t0_cs HP2 HS EE | exact R23]|].
    split; [transitivity (getr regs3 20); [t0_cs HP2 HS EE | exact R20]|].
    split; [transitivity (getr regs3 21); [t0_cs HP2 HS EE | exact R21]|].
    split; [transitivity (getr regs3 24); [t0_cs HP2 HS EE | exact R24]|].
    split; [transitivity (getr regs3 19); [t0_cs HP2 HS EE | exact R19]|].
    transitivity (getr regs3 9); [t0_cs HP2 HS EE | exact R9]. }
  rewrite Hv, Hvl, length_skipn. reflexivity.
Qed.

Theorem tk_seg_T0_holds : tk_seg_T0 B.
Proof.
  intros cx i d f name nl ns nl2 close HLf HLH ly3 S3 W3 regs3 mem3 md3 HT.
  destruct HT as (HB & HC & HSL & (R23 & R22 & R18 & R8) & Hsc & Hit & Hsd & Hdc & Hm & V8 & V28 &
    R20 & R21 & R24 & R19 & R9).
  apply (t0_A cx (mkTKP i d f name nl ns nl2 close) ly3 S3 W3 regs3 mem3 md3 HLf HLH).
  - exact (conj (conj HB (conj Hsc (conj Hit (conj Hsd (conj Hdc Hm))))) (conj HC (conj HSL (conj V8 V28)))).
  - exact (conj R8 (conj R18 (conj R22 (conj R23 (conj R20 (conj R21 (conj R24 (conj R19 R9)))))))).
Qed.
End c.

About tk_seg_T0_holds.
Print Assumptions tk_seg_T0_holds.
