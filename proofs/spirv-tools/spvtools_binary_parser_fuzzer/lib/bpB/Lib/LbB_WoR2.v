(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit LbB_DStat LbB_WoR1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_CTXCK : Z := 0xeb07c.

Definition WO_SH2A : list Z :=
  repeat 0xf1 4 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 2 ++
  repeat 0xf2 2 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 4 ++ repeat 0xf2 4 ++ repeat 0xf8 50 ++
  repeat 0xf2 8 ++ repeat 0xf8 30 ++ repeat 0xf2 8 ++ repeat 0xf8 30 ++ repeat 0xf2 8 ++ repeat 0 8 ++
  repeat 0xf2 4 ++ repeat 0xf8 36 ++ repeat 0xf3 8.

Definition WO_PU : Z := 0xeb24c.

Definition WO_SH2C : list Z :=
  repeat 0xf1 4 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 2 ++
  repeat 0xf2 2 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 4 ++ repeat 0xf2 4 ++ repeat 0xf8 50 ++
  repeat 0xf2 8 ++ repeat 0xf8 30 ++ repeat 0xf2 8 ++ repeat 0xf8 30 ++ repeat 0xf2 8 ++ repeat 0 8 ++
  repeat 0xf2 4 ++ repeat 0 36 ++ repeat 0xf3 8.


Lemma kword1_of_u8arr : forall E m A bs (i : nat) (a : saddr) (v : Z),
  u8arr asegs m A bs -> nth_error bs i = Some (Z_to_bv 8 v) -> 0 <= v < 256 ->
  estart E a = A + Z.of_nat i -> 0 <= A -> (i < length bs)%nat ->
  kentry_ok asegs E m (KWord a 1 (ELit v)).
Proof.
  intros E m A bs i a v [B _] Hn Hv Hs H0 Hi. pose proof B as (B0 & B1 & _). cbn [kentry_ok].
  split; [lia|]. split; [unfold flat; lia|].
  rewrite (adenot_of_estart E a (A + Z.of_nat i) Hs ltac:(lia)).
  cbn [edenot]. rewrite word_to_le_bytes_1 by lia.
  destruct B as (_ & _ & B). specialize (B i Hi). rewrite Hn in B.
  apply rdn1_of_mrd. exact B.
Qed.

Lemma q64 : forall ff, 0 <= ff < 2 ^ 47 -> ff mod 64 = 0 -> mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff.
Proof. intros ff H1 H2. rewrite w_mul by (Z.div_mod_to_equations; lia). f_equal. Z.div_mod_to_equations. lia. Qed.
Lemma sh_q : forall ff, 0 <= ff < 2 ^ 47 -> ff mod 64 = 0 ->
  mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000).
Proof.
  intros ff H1 H2. rewrite w_mul by (Z.div_mod_to_equations; lia). f_equal.
  unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
Qed.

Lemma sh_c16 : forall ctx, 0 <= ctx < 2 ^ 47 -> ctx mod 16 = 0 ->
  mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 (ctx / 16)) = Z_to_bv 64 (sh ctx - 0x7fff8000).
Proof.
  intros ctx H1 H2. rewrite w_mul by (Z.div_mod_to_equations; lia). f_equal.
  unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
Qed.
Lemma q16 : forall ctx, 0 <= ctx < 2 ^ 47 -> ctx mod 16 = 0 -> mul_div M_MUL (Z_to_bv 64 16) (Z_to_bv 64 (ctx / 16)) = Z_to_bv 64 ctx.
Proof. intros ctx H1 H2. rewrite w_mul by (Z.div_mod_to_equations; lia). f_equal. Z.div_mod_to_equations. lia. Qed.

Ltac lgc Hlf k dj :=
  eapply (rw_cells_log_nth _ _ _ k);
  [ exact Hlf | reflexivity
  | cbn [firstn]; repeat (apply Forall_cons; [dj |]); apply Forall_nil
  | dj | | reflexivity | exact I | try (first [ reflexivity | HLib.evs; reflexivity ]) ].

Fixpoint nb_inside (bs : list (expr * list (Z * Z))) (se : sentry) : bool :=
  match bs with
  | [] => false
  | (b, W) :: bs' => (expr_eqb (a_base (e_addr se)) b && sb_inside W (a_off (e_addr se)) (Z.of_nat (e_width se)))
                     || nb_inside bs' se
  end.

Fixpoint nb_wins (E : env) (bs : list (expr * list (Z * Z))) : list (Z * Z) :=
  match bs with
  | [] => []
  | (b, W) :: bs' => map (fun iv : Z * Z => (bv_unsigned (edenot E b) + fst iv, bv_unsigned (edenot E b) + snd iv)) W
                     ++ nb_wins E bs'
  end.

Lemma munch_mem_denot_nb : forall bs W E M log,
  log_flat E log -> forallb (nb_inside bs) log = true -> nb_wins E bs = W -> munch W M (mem_denot E M log).
Proof.
  intros bs W E M log Hf Hb HW. subst W. apply munch_mem_denot; [exact Hf|].
  apply Forall_forall. intros se Hse. rewrite forallb_forall in Hb. specialize (Hb se Hse).
  assert (IA : forall X Y a n, inside X a n \/ inside Y a n -> inside (X ++ Y) a n).
  { induction X as [|[lo hi] X IH]; intros Y a n [K|K]; cbn in *; [destruct K | exact K | destruct K as [K|K]; [left; exact K | right; apply IH; left; exact K]
      | right; apply IH; right; exact K]. }
  revert Hb. induction bs as [|[b W] bs IH]; intros Hb; cbn [nb_inside nb_wins] in Hb |- *; [discriminate|].
  apply IA. apply orb_true_iff in Hb. destruct Hb as [Hb|Hb].
  - left. apply andb_true_iff in Hb as [Hbe Hi]. apply expr_eqb_true in Hbe. unfold estart. rewrite Hbe. apply sb_inside_sound. exact Hi.
  - right. apply IH. exact Hb.
Qed.

Fixpoint nb_out (bs : list (expr * Z * Z)) (se : sentry) : bool :=
  match bs with
  | [] => false
  | (b, lo, hi) :: bs' => (expr_eqb (a_base (e_addr se)) b && (lo <=? a_off (e_addr se))
                           && (a_off (e_addr se) + Z.of_nat (e_width se) <=? hi)) || nb_out bs' se
  end.

Lemma rw_cells_log_nth_nb : forall E M lg (k : nat) (a : saddr) (w : nat) (v : expr) (A : Z) (c : cell) bs,
  log_flat E lg -> nth_error lg k = Some (SE a w v) ->
  forallb (nb_out bs) (firstn k lg) = true ->
  Forall (fun t : expr * Z * Z => A + Z.of_nat w <= bv_unsigned (edenot E (fst (fst t))) + snd (fst t)
                                  \/ bv_unsigned (edenot E (fst (fst t))) + snd t <= A) bs ->
  estart E a = A -> wr_at asegs M A (Z.of_nat w) ->
  csize c = w -> cell_wf c -> cbytes c = word_to_le_bytes w (edenot E v) ->
  rw_cells asegs (mem_denot E M lg) A [c].
Proof.
  intros E M lg k a w v A c bs Hf Hn Hd HD Hs HW Hc Hwf Hb.
  eapply (rw_cells_log_nth E M lg k a w v A c Hf Hn); [| exact Hs | exact HW | exact Hc | exact Hwf | exact Hb].
  apply Forall_forall. intros e' He'. cbv beta. rewrite forallb_forall in Hd. specialize (Hd e' He'). rewrite Hs.
  revert HD Hd. induction bs as [|[[b lo] hi] bs IH]; intros HD Hd; cbn [nb_out] in Hd; [discriminate|].
  apply Forall_cons_iff in HD as [HD1 HD2]. cbn [fst snd] in HD1.
  apply orb_true_iff in Hd. destruct Hd as [Hd|Hd].
  - apply andb_true_iff in Hd as [Hd H2]. apply andb_true_iff in Hd as [Hbe H1]. apply expr_eqb_true in Hbe.
    apply Z.leb_le in H1, H2. unfold estart. rewrite Hbe. lia.
  - exact (IH HD2 Hd).
Qed.

Section WoR2.
  Context {HCEIL : HeapCeil}.

  Definition w2a_post (gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff ctx lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (sh ctx)) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ctx) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000)
                    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s11 x28 x29 x30 x31) F (Z_to_bv 64 WO_CTXCK) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 80, S1 + 88); (ff, ff + 24); (sh ff, sh ff + 476)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 80) [C8 (Z_to_bv 64 ff)]
      /\ rw_cells asegs m1 ff [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x2187b); C8 (Z_to_bv 64 0xea7c4)]
      /\ u8arr asegs m1 (sh ff) (map (Z_to_bv 8) WO_SH2A).

  Lemma w2a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff ctx lo : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 3808 <= S1 -> (sh ff + 476 <= ff \/ ff + 3808 <= sh ff) ->
    ctx mod 16 = 0 -> 0 < ctx -> ctx + 64 <= 2 ^ 47 ->
    wr_at asegs m ff 24 -> u8arr asegs m (sh ff) (map (Z_to_bv 8) (repeat 0 476)) -> relro0 m ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (w2a_post gp tp s11 F fc SP S1 ff ctx lo m)
      (MS (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ctx) s3 s4 s5 (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) s11 x28 x29 x30 x31) F (Z_to_bv 64 WO_SM_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 FSH C16 CLO CHI WF US RO ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (QC : mul_div M_MUL (Z_to_bv 64 16) (Z_to_bv 64 (ctx / 16)) = Z_to_bv 64 ctx) by (apply q16; lia).
    assert (QCS : mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 (ctx / 16)) = Z_to_bv 64 (sh ctx - 0x7fff8000)) by (apply sh_c16; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 476 <= 2 ^ 45)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHC : 0x7fff8000 <= sh ctx /\ sh ctx + 8 <= 0x10007fff8000)
      by (clear - CLO CHI; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (WS : wr_at asegs m (sh ff) 476).
    { destruct US as (_ & (W1 & W2 & W)). rewrite length_map, repeat_length in W2, W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. lia. }
    assert (WT80 : forall a n, S1 + 80 <= a -> a + n <= S1 + 88 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    remember (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ctx) s3 s4 s5 (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 (ctx / 16); Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EMd M_MUL (ELit 64) (EVar 32)); (18%bv, EMd M_MUL (ELit 16) (EVar 33));
                                       (23%bv, ELit 2147450880); (9%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; [rewrite Q; reflexivity | rewrite QC; reflexivity]. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - 0x7fff8000)
      by (evs; rewrite QS, u64_of_Z by lia; reflexivity).
    assert (E1 : bv_unsigned (edenot E (EVar 34)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 24);
         KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 476);
         KWr (SA (EVar 34) 80) (ELit 8);
         KImg 0x17e000 0x186000;
         KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 33) 0 (2 ^ 43) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E1; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite E1; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { exact (kimg_relro E m RO). }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_SM_RA m (seg_rom asegs) HR HK 600%nat [WO_CTXCK] (SCR [true] [] []) 60%N.
    { split_scs. all: try (cbn [sc_denot]; evs; rewrite QC; rewrite br_ne by lia; apply negb_true_iff, Z.eqb_neq; lia).
      all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF, ?ES, ?E1, ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21.
    rreg HR' 23%bv L23.
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (sh ctx)) by (rewrite L10, QCS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L18' : getr R' 18 = Z_to_bv 64 ctx) by (rewrite L18; exact QC).
    assert (L19' : getr R' 19 = Z_to_bv 64 (sh ff)) by (rewrite L19, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L20' : getr R' 20 = Z_to_bv 64 ff) by (rewrite L20; exact Q).
    assert (L21' : getr R' 21 = Z_to_bv 64 ff) by (rewrite L21; exact Q).
    assert (MU1 : munch [(S1 + 80, S1 + 88); (ff, ff + 24); (sh ff, sh ff + 476)] m M1).
    { subst M1. eapply (munch_mem_denot_nb [(EVar 34, [(80, 88)]); (EMd M_MUL (ELit 64) (EVar 32), [(0, 24)]);
                                            (EMd M_MUL (ELit 8) (EVar 32), [(SHBASE, SHBASE + 476)])]);
        [exact Hlf | vm_compute; reflexivity |].
      cbn [nb_wins map app fst snd]. rewrite E1, EF, ES. unfold SHBASE.
      repeat (apply f_equal2; [apply f_equal2; lia|]). reflexivity. }
    assert (CS1 : rw_cells asegs M1 (S1 + 80) [C8 (Z_to_bv 64 ff)]).
    { subst M1. eapply (rw_cells_log_nth_nb _ _ _ 487%nat _ _ _ _ _
                          [(EMd M_MUL (ELit 64) (EVar 32), 0, 24); (EMd M_MUL (ELit 8) (EVar 32), SHBASE, SHBASE + 476)]);
        [exact Hlf | reflexivity | vm_compute; reflexivity
        | repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?EF, ?ES; unfold SHBASE; lia|]); apply Forall_nil
        | unfold estart; cbn [a_base a_off]; rewrite E1; reflexivity
        | apply WT80; lia | reflexivity | exact I
        | evs; rewrite Q; reflexivity ]. }
    assert (CH1 : rw_cells asegs M1 ff [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x2187b); C8 (Z_to_bv 64 0xea7c4)]).
    { assert (WF' : forall a, ff <= a -> a + 8 <= ff + 24 -> wr_at asegs m a 8).
      { intros a X1 X2. destruct WF as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros i Hi.
        replace (a + i) with (ff + (a - ff + i)) by lia. apply W. lia. }
      assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
      assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
      subst M1. clear - Hlf EF ES' WF' Q F64 FLO FS1 FSH SHL SHB S1H SPH.
      apply rw_cells_cons8_c; [lgcell3 Hlf EF (EMd M_MUL (ELit 8) (EVar 32)) SHBASE (SHBASE + 476) WF' 486%nat|].
      apply rw_cells_cons8_c; [lgcell3 Hlf EF (EMd M_MUL (ELit 8) (EVar 32)) SHBASE (SHBASE + 476) WF' 485%nat|].
      lgcell3 Hlf EF (EMd M_MUL (ELit 8) (EVar 32)) SHBASE (SHBASE + 476) WF' 484%nat. }
    assert (US1 : u8arr asegs M1 (sh ff) (map (Z_to_bv 8) WO_SH2A)).
    { assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
      assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
      assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
      subst M1. lazymatch type of ES with bv_unsigned ?t = _ => replace (sh ff) with (bv_unsigned t + SHBASE) by (rewrite ES; unfold SHBASE; lia) end.
      lazymatch type of Hlf with log_flat _ ?lg =>
        let l := eval vm_compute in (others (EMd M_MUL (ELit 8) (EVar 32)) lg) in
        assert (HO : others (EMd M_MUL (ELit 8) (EVar 32)) lg = l) by (vm_cast_no_check (@eq_refl _ l)) end.
      eapply u8arr_mem_denot with (base := repeat 0 476); [exact Hlf | | rewrite ES; unfold SHBASE; lia | rewrite ES, repeat_length; unfold SHBASE; lia
                              | rewrite ES; replace (sh ff - 0x7fff8000 + SHBASE) with (sh ff) by (unfold SHBASE; lia); exact US
                              | vm_cast_no_check (@eq_refl _ (Some WO_SH2A))].
      intros i Hi. rewrite repeat_length in Hi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi.
      apply (lmiss_of_others _ _ _ _ 476); [| lia]. rewrite HO.
      clear - ES' EF' E1 SHB FSH SHL F64 FLO FS1 S1L S1H SPH.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?EF', ?ES', ?u64_of_Z by lia; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L9', L10', L18', L19', L20', L21', L23.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. split; [exact CS1|]. split; [exact CH1 | exact US1].
  Qed.

  Definition w2bc_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff ctx tenv lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    x10 x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ctx) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000)
                    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3360)) x28 x29 x30 x31) F (Z_to_bv 64 WO_PU) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 48, S1 + 64); (ff + 3360, ff + 3364); (ff + 3408, ff + 3416); (sh ff + 432, sh ff + 468)] m m1
      /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 48) [C8 (Z_to_bv 64 (ff + 2224)); C8 (Z_to_bv 64 (ff + 3376))]
      /\ rw_cells asegs m1 (ff + 3360) [C4 (Z_to_bv 64 tenv)]
      /\ rw_cells asegs m1 (ff + 3408) [C8 (Z_to_bv 64 0)]
      /\ u8arr asegs m1 (sh ff) (map (Z_to_bv 8) WO_SH2C).

  Lemma w2bc : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff ctx tenv lo : Z) j1 j2,
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 3808 <= 2 ^ 47 -> (sh ff + 476 <= ff \/ ff + 3808 <= sh ff) ->
    ctx mod 16 = 0 -> 0 <= ctx -> ctx + 64 <= S1 -> (ctx + 64 <= ff \/ ff + 3808 <= ctx) -> 0 <= tenv < 19 ->
    (ff + 3808 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) -> ff + 3808 <= S1 ->
    rw_cells asegs m ctx [C4 (Z_to_bv 64 tenv); CB 44 j1; C8 (Z_to_bv 64 0); CB 8 j2] -> addressable m ctx 64 ->
    wr_at asegs m (ff + 3360) 56 -> u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2A) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (w2bc_post gp tp F fc SP S1 ff ctx tenv lo m)
      (MS (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               (Z_to_bv 64 (sh ctx)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ctx) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s11 x28 x29 x30 x31) F (Z_to_bv 64 WO_CTXCK) fc None m (seg_rom asegs)).
  Proof.
    intros until j2. intros S1L S1H SPH LO F64 FLO FHI FSH C16 CLO CS1 CFF ENV FAPP FS1 CC CA WF US ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (QC : mul_div M_MUL (Z_to_bv 64 16) (Z_to_bv 64 (ctx / 16)) = Z_to_bv 64 ctx) by (apply q16; lia).
    assert (QCS : mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 (ctx / 16)) = Z_to_bv 64 (sh ctx - 0x7fff8000)) by (apply sh_c16; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 476 <= 0x10007fff8000)
      by (clear - FLO FHI; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHC : 0x7fff8000 <= sh ctx /\ sh ctx + 8 <= 0x10007fff8000 /\ sh ctx = ctx / 8 + 0x7fff8000)
      by (clear - CLO CS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    assert (EC' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 16) (Z_to_bv 64 (ctx / 16))) = ctx) by (rewrite QC, u64_of_Z by lia; reflexivity).
    assert (ECS' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 (ctx / 16))) = sh ctx - 0x7fff8000) by (rewrite QCS, u64_of_Z by lia; reflexivity).
    assert (WS : wr_at asegs m (sh ff) 476).
    { destruct US as (_ & (W1 & W2 & W)). rewrite length_map in W2, W. cbn [length WO_SH2A app repeat] in W2, W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. cbn. lia. }
    assert (SCA : u8arr asegs m (sh ctx) (shadow_of 64)) by (destruct CA as (_ & _ & _ & X); exact X).
    remember (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               (Z_to_bv 64 (sh ctx)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ctx) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 (ctx / 16); Z_to_bv 64 S1; Z_to_bv 64 tenv]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 34);
                   (10%bv, EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 33)) (ELit 2147450880));
                   (18%bv, EMd M_MUL (ELit 16) (EVar 33));
                   (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
                   (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EMd M_MUL (ELit 64) (EVar 32));
                   (22%bv, ELit 0); (23%bv, ELit 2147450880); (24%bv, ELit 0); (25%bv, ELit 0); (26%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity); try (rewrite QC; reflexivity).
      - transitivity (Z_to_bv 64 (sh ctx)); [reflexivity|]. rewrite QCS, w_add by lia. f_equal. lia.
      - transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]. rewrite QS, w_add by lia. f_equal. lia. }
    assert (ESb : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - 0x7fff8000)
      by (evs; rewrite QS, u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 2) (EVar 33)) SHBASE) 1 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 16) (EVar 33)) 0) 4 (EVar 35);
        KWord (SA (EMd M_MUL (ELit 2) (EVar 33)) (SHBASE + 6)) 1 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 16) (EVar 33)) 48) 8 (ELit 0);
        KWr (SA (EVar 34) 48) (ELit 16);
        KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 3360) (ELit 56);
        KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) (SHBASE + 432)) (ELit 36);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 33) 0 (2 ^ 43); KRange (EVar 34) (2 ^ 45) (2 ^ 47);
        KRange (EVar 35) 0 18 ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword1_of_u8arr E m (sh ctx) _ 0%nat); [exact SCA | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite ECS'; unfold SHBASE; lia | lia | change (length (shadow_of 64)) with 8%nat; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m ctx _ 0%nat (C4 (Z_to_bv 64 tenv))); [exact CC | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite EC'; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword1_of_u8arr E m (sh ctx) _ 6%nat); [exact SCA | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite ECS'; unfold SHBASE; lia | lia | change (length (shadow_of 64)) with 8%nat; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m ctx _ 48%nat (C8 (Z_to_bv 64 0))); [exact CC | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite EC'; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; evs; rewrite ES'; unfold SHBASE; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ES', u64_of_Z by lia; unfold SHBASE; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_CTXCK m (seg_rom asegs) HR HK 200%nat [WO_PU] (SCR [] [] []) 60%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?EC', ?ECS', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 9%bv L9. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 ctx) by (rewrite L18; exact QC).
    assert (L19' : getr R' 19 = Z_to_bv 64 (sh ff)) by (rewrite L19, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L20' : getr R' 20 = Z_to_bv 64 ff) by (rewrite L20; exact Q).
    assert (L21' : getr R' 21 = Z_to_bv 64 ff) by (rewrite L21; exact Q).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 3360)) by (rewrite L27, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (MU1 : munch [(S1 + 48, S1 + 64); (ff + 3360, ff + 3364); (ff + 3408, ff + 3416); (sh ff + 432, sh ff + 468)] m M1).
    { subst M1. clear - Hlf F64 FLO FHI SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WSS : forall a n, S1 + 48 <= a -> a + n <= S1 + 64 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (WFF : forall a n, ff + 3360 <= a -> a + n <= ff + 3416 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 3360 + (a - (ff + 3360) + i)) by lia. apply W. lia. }
    assert (CSP1 : rw_cells asegs M1 (S1 + 48) [C8 (Z_to_bv 64 (ff + 2224)); C8 (Z_to_bv 64 (ff + 3376))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FHI FSH FAPP FS1 S1L S1H SPH WSS Q.
      apply rw_cells_cons8_c.
      - lgc Hlf 39%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia).
        + apply WSS; cbn; lia.
        + HLib.evs. rewrite Q. rewrite ?w_add, ?v_addi_Z by lia. reflexivity.
      - lgc Hlf 37%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia).
        + apply WSS; cbn; lia.
        + HLib.evs. rewrite Q. rewrite ?w_add, ?v_addi_Z by lia. reflexivity. }
    assert (CE1 : rw_cells asegs M1 (ff + 3360) [C4 (Z_to_bv 64 tenv)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FHI FSH FAPP FS1 S1L S1H SPH WFF Q.
      lgc Hlf 38%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia).
      apply WFF; cbn; lia. }
    assert (CF1 : rw_cells asegs M1 (ff + 3408) [C8 (Z_to_bv 64 0)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FHI FSH FAPP FS1 S1L S1H SPH WFF Q.
      lgc Hlf 36%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia).
      apply WFF; cbn; lia. }
    assert (US1 : u8arr asegs M1 (sh ff) (map (Z_to_bv 8) WO_SH2C)).
    { subst M1. lazymatch type of ESb with bv_unsigned ?t = _ => replace (sh ff) with (bv_unsigned t + SHBASE) by (rewrite ESb; unfold SHBASE; lia) end.
      lazymatch type of Hlf with log_flat _ ?lg =>
        let l := eval vm_compute in (others (EMd M_MUL (ELit 8) (EVar 32)) lg) in
        assert (HO : others (EMd M_MUL (ELit 8) (EVar 32)) lg = l) by (vm_cast_no_check (@eq_refl _ l)) end.
      eapply u8arr_mem_denot with (base := WO_SH2A); [exact Hlf | | rewrite ESb; unfold SHBASE; lia | rewrite ESb; unfold SHBASE; cbn [length WO_SH2A app repeat]; lia
                              | rewrite ESb; replace (sh ff - 0x7fff8000 + SHBASE) with (sh ff) by (unfold SHBASE; lia); exact US
                              | vm_cast_no_check (@eq_refl _ (Some WO_SH2C))].
      intros i Hi. cbn [length WO_SH2A app repeat Z.of_nat Pos.of_succ_nat Pos.succ] in Hi.
      apply (lmiss_of_others _ _ _ _ 476); [| lia]. rewrite HO.
      clear - ES' EF' EC' SHB FSH SHL F64 FLO FHI FAPP FS1 S1L S1H SPH.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?EF', ?ES', ?u64_of_Z by lia; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L9', L18', L19', L20', L21', L22, L23, L24, L25, L26, L27'.
    apply evt_done.
    do 15 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. split; [exact CSP1|]. split; [exact CE1|]. split; [exact CF1 | exact US1].
  Qed.
End WoR2.
