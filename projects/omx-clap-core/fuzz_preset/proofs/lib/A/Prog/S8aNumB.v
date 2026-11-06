(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, unstripped twin bff8519b), ex_value piece 5
   (ev_number, fuzz_preset.c fa3e896698eb :243-264 (#102 source) inlined), sub-piece B: the scan loop, CL (+0x364, 0x83608) ->
   CS (+0x8c0, 0x83b64), over the ONE image-A program listing (lib/A/Listing_prog.v, ex_value = slot 1841), generic in
   the image facts (Context PAImg) and the allocator relation ARx (LAWS : AR_laws_x, its head length hl a Context).
   Proves ev_B_stmt (S8aNumCut.v).
   Code (neutral listing, the internal file ex_value.fuzz_preset.asan.s): +0x364 .. +0x3a0 the loop, the shadow check of a0 with
   its slow arm +0x3a4 .. +0x3a8 (absorbed by the runner; the report call at +0x3ac is never reached: the byte is
   addressable by src_rd), +0x8bc `mv s6, a2`. One iteration is one runner pass from CL to CL or to CS; the loop is
   nat induction on len - j. Engine: YC80x / YC1fPx (paj_run_x, paj_run_to_x) over YCbqG's ajournal_x. The loop writes
   no memory, so the cursor invariant ev_mid carries over with the runner's journal (no ev_mid_keep_stmt needed), and
   the frame shadow fact ev_fsh W mem carries over unchanged (same W, same mem). MEMNORM: ev_mid's last conjunct
   YAkMemnorm.memnorm segs mem (S8aIface.v) is a fact of that same mem (nb_frame: every pass keeps the whole memory),
   so the CL / CS MID takes it from CL's MID as it is (nb_mk_CL, nb_CS_common: proj2 HMID); no YSRrMemnorm *_inv twin
   is needed.
   Numerals: 7364 (DERIVED: slot 1841 * 4); 0x364, 0x8c0 (LENGTH: offsets in ex_value, measured from the listing);
   8232 = 7364 + 0x364, 9604 = 7364 + 0x8c0 (DERIVED); -11 58 -58 -43 1 (WORD: the listing's immediates);
   288230376218820621 (WORD: the mask the listing builds at +0x34c..+0x360, = S8aNumPure.MASK); 2147450880
   (DERIVED: SHADOW_OFF's value as the runner prints it); 2 ^ 44 (LENGTH: the shadow band); 140737479966720
   (LENGTH: YM05's CEIL_MAX, the bound of every run's alloc_ceiling); 4096, 255, 256, 2 ^ 64 (LENGTH: address and
   byte ranges); register numbers 2 .. 27 and atom numbers 32, 512, 513 (WORD / LENGTH: the env's register atoms,
   its first extra atom, the runner's token atoms). Section Hypotheses: LAWS and Hent only. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aNumPure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- pure: the loop's three byte tests as the runner leaves them, against PjGrammar.numch ---- *)
(* +0x37c `bltu a3(-11), a7(b - 58)`: taken on a digit *)
Definition nb_fd (b : Z) : bool :=
  branch_taken BC_LTU (Z_to_bv 64 (-11)) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 b) + -58)).
(* +0x384 `bltu a4(58), a6(b - 43)`: taken (stop) when b - 43 is above 58 unsigned *)
Definition nb_fr (b : Z) : bool :=
  branch_taken BC_LTU (Z_to_bv 64 58) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 b) + -43)).
(* +0x390 `beqz ((MASK >> (b - 43)) & 1)`: taken (stop) when the mask bit is clear *)
Definition nb_ft (b : Z) : bool :=
  branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 288230376218820621)
    (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 b) + -43))) (Z_to_bv 64 1)) (Z_to_bv 64 0).

Lemma nb_bytes_all : forallb (fun b => Bool.eqb (PjGrammar.numch b) (nb_fd b || (negb (nb_fr b) && negb (nb_ft b))))
  S8aNumPure.bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nb_numch : forall b, 0 <= b < 256 -> PjGrammar.numch b = nb_fd b || (negb (nb_fr b) && negb (nb_ft b)).
Proof.
  intros b Hb. pose proof (S8aNumPure.forallb_bytes256 _ nb_bytes_all b Hb) as H. cbv beta in H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma nb_digit_numch : forall b, PjGrammar.digit b = true -> PjGrammar.numch b = true.
Proof. intros b H. unfold PjGrammar.numch. rewrite H. reflexivity. Qed.

Lemma nb_firstn_S : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  induction l as [|h t IH]; intros n Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. cbn in Hn. lia.
Qed.

Lemma nb_len_skipn : forall (l : list Z) n, length (skipn n l) = (length l - n)%nat.
Proof. induction l as [|h t IH]; intros n; destruct n; cbn; try reflexivity; apply IH. Qed.

Lemma nb_nth_skipn : forall (l : list Z) n m, nth m (skipn n l) 0 = nth (n + m) l 0.
Proof.
  induction l as [|h t IH]; intros n m.
  - rewrite skipn_nil. destruct m, n; reflexivity.
  - destruct n as [|n]; cbn [skipn]; [reflexivity | exact (IH n m)].
Qed.

Lemma nb_span_step : forall (x : list Z) j0 j, (j0 <= j < length x)%nat ->
  Forall (fun z => PjGrammar.numch z = true) (ev_sub x j0 j) -> PjGrammar.numch (nth j x 0) = true ->
  Forall (fun z => PjGrammar.numch z = true) (ev_sub x j0 (S j)).
Proof.
  intros x j0 j Hj HF Hn. unfold ev_sub in *.
  replace (S j - j0)%nat with (S (j - j0)) by lia.
  rewrite nb_firstn_S by (rewrite nb_len_skipn; lia).
  apply Forall_app. split; [exact HF|]. constructor; [|constructor].
  rewrite nb_nth_skipn. replace (j0 + (j - j0))%nat with j by lia. exact Hn.
Qed.

Lemma nb_ltu_lit : forall u v, 0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 u) (Z_to_bv 64 v) = (u <? v).
Proof. intros u v Hu Hv. cbn [branch_taken]. unfold bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma nb_w64 : forall u v, u = v -> Z_to_bv 64 u = w64 v.
Proof. intros u v ->. reflexivity. Qed.

(* ---- the symbolic state at CL (pc 8232 = ex_value's slot * 4 + 0x364): a0 and s6 the atom of s6 (x0 + j), the
   loop constants a3 a4 a5 and s8 (SHADOW_OFF) literal, the byte x[j] the one-byte read-only region at s6 holding
   atom 32 (the env's extra word); the shadow byte of a0 is the runner's token, its obligation src_rd's ---- *)
Definition NB_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 13%bv (SLit (-11))) 14%bv (SLit 58))
    15%bv (SLit 288230376218820621)) 24%bv (SLit SHADOW_OFF)) 10%bv (SOff 22 0).
Definition NB_mem : smem := [YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]].
(* atom 22's range: [4096, CEIL_MAX] (LENGTH: YM05's bound on every run's alloc_ceiling) *)
Definition NB_facts : facts := mkFacts [(22%nat, mkAF 4096 140737479966720 0); (32%nat, mkAF 0 255 0)] [] [].
Definition NB_ss : sstate := mkSS 8232 NB_regs NB_mem None NB_facts.
Definition NB_Bx : sv := SLit SHADOW_OFF.
Definition NB_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the registers the loop never writes, the ones CL / CS name *)
Definition NB_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 11; 12; 18; 19; 21; 23; 25; 26; 27]%bv.

Definition nb_kept_ok (ss : sstate) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NB_KEPT.
Definition nb_resv_none (ss : sstate) : bool := match ss_resv ss with None => true | Some _ => false end.
(* the three cut shapes the runner stops in: back at CL with s6 = a0 = x0 + j + 1; at CS with s6 = x0 + j (a stop
   byte); at CS through +0x8bc with s6 = a2 = x0 + len *)
Definition nb_shape_loop (ss : sstate) : bool :=
  (ss_pc ss =? 8232) && nb_resv_none ss && nb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 22 1) && sv_eqb (sr_get (ss_regs ss) 10%bv) (SOff 22 1) &&
  sv_eqb (sr_get (ss_regs ss) 13%bv) (SLit (-11)) && sv_eqb (sr_get (ss_regs ss) 14%bv) (SLit 58) &&
  sv_eqb (sr_get (ss_regs ss) 15%bv) (SLit 288230376218820621) &&
  sv_eqb (sr_get (ss_regs ss) 24%bv) (SLit 2147450880).
Definition nb_shape_stop (ss : sstate) : bool :=
  (ss_pc ss =? 9604) && nb_resv_none ss && nb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 22 0) && sv_eqb (sr_get (ss_regs ss) 24%bv) (SLit 2147450880).
Definition nb_shape_end (ss : sstate) : bool :=
  (ss_pc ss =? 9604) && nb_resv_none ss && nb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 12 0) && sv_eqb (sr_get (ss_regs ss) 24%bv) (SLit 2147450880).

(* the loop writes nothing: every runner pass keeps the whole memory *)
Lemma nb_frame : forall E ss (m m' : word -> option byte), frame_of E (ss_mem ss) m m' -> ss_mem ss = NB_mem -> m' = m.
Proof.
  intros E ss m m' HF Hs. apply functional_extensionality. intros x. apply HF. rewrite Hs.
  intros (r & Hin & Hr). unfold NB_mem in Hin. destruct Hin as [<-|[]]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

Ltac nb_agree HAE :=
  lazymatch goal with
  | |- env_agree ?kk _ (ewset ?X ?n ?v) =>
      apply (YP03.env_agree_trans kk _ X); [nb_agree HAE | apply (YP03.env_agree_le kk n); [lia | apply env_agree_ewset]]
  | |- _ => exact HAE
  end.

Ltac nb_mem mem0 :=
  lazymatch goal with HF : frame_of _ _ _ (ms_mem _) |- _ =>
    let Hm := fresh "Hm" in
    pose proof (nb_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm; clear HF
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  try match goal with
  | Hold : ms_mem ?m0 = mem0, Hnew : ms_mem _ = ms_mem ?m0 |- _ => rewrite Hold in Hnew; clear Hold
  end;
  repeat match goal with HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progress (rewrite ?wvb_collapse in HJ) end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val rc A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* image fact of the instance (PRW_pj_write.v's Hent form), discharged at PI_prog_A by A_entry_ex_value *)
Hypothesis Hent : SIGMA AS_ex_value = BASE + 7364.

#[local] Abbreviation AJ a ly Sa Hp W mem md k := (ajournal_x (SK := SK) SEGS B (@prh_pst PI) ARx (ea_STK a + ea_d a)
  (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)]
  ly Sa Hp W mem md k).

Lemma nb_cfg : forall (fxc : YK11.FPState) regs pc off mem md, pc = 7364 + off ->
  @ev_cfg rc A_prog_listing PA fxc regs off mem md = mkCfg (@mkst fxc regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)) md.
Proof. intros fxc regs pc off mem md ->. unfold ev_cfg, ev_pc. rewrite Hent. rewrite Z.add_assoc. reflexivity. Qed.

Lemma nb_reg_of : forall (fxc : YK11.FPState) (H : word -> bool) E ss ms (r : bv 5) e,
  @st_ok_pi SEGS VAL fxc E ss (restrict H ms) -> sv_eqb (sr_get (ss_regs ss) r) e = true ->
  getr (ms_regs ms) r = sv_denot E e.
Proof. intros fxc H E ss ms r e HS Hq. apply sv_eqb_eq in Hq. rewrite <- Hq. exact (st_ok_pi_restrict_reg H E ss ms r HS). Qed.

(* ---- the cut facts at the next cut, from CL's and the runner's (no machine state here) ---- *)
Lemma nb_mk_CL : forall a W regs regs' mem md md' ly Sa Hp k i1 c j,
  @ev_CL rc cp PI RL A_prog_listing PA B ARx SK a W regs mem md ly Sa Hp k i1 c j ->
  AJ a ly Sa Hp W mem md' k ->
  (forall r, In r NB_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 22 = Z_to_bv 64 (ea_x0 a + Z.of_nat j + 1) -> getr regs' 10 = Z_to_bv 64 (ea_x0 a + Z.of_nat j + 1) ->
  getr regs' 13 = Z_to_bv 64 (-11) -> getr regs' 14 = Z_to_bv 64 58 ->
  getr regs' 15 = Z_to_bv 64 288230376218820621 -> getr regs' 24 = Z_to_bv 64 2147450880 ->
  PjGrammar.numch (nth j (ea_x a) 0) = true -> (S j < length (ea_x a))%nat ->
  @ev_CL rc cp PI RL A_prog_listing PA B ARx SK a W regs' mem md' ly Sa Hp k i1 c (S j).
Proof.
  intros a W regs regs' mem md md' ly Sa Hp k i1 c j HCL HJ HK Q22 Q10 Q13 Q14 Q15 Q24 Hn Hlt.
  destruct HCL as (HMID & HB & HSC & HSP & Hj & R22 & R10 & R13 & R14 & R15 & HFS).
  destruct HB as (HR & R23 & HB').
  destruct HSC as (R27 & V112 & R21 & R11 & R12).
  destruct HSP as (HLD & HSF).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ HFS)))))))))).
  - split; [exact HJ | exact (proj2 HMID)].
  - split; [|split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23 | exact HB']].
    destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    all: first [ exact Q24 | lazymatch goal with |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption end ].
  - refine (conj _ (conj V112 (conj _ (conj _ _)))).
    all: lazymatch goal with |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption end.
  - split; [exact HLD|]. apply nb_span_step; [lia | exact HSF | exact Hn].
  - lia.
  - rewrite Q22. apply nb_w64. lia.
  - rewrite Q10. apply nb_w64. lia.
  - exact Q13.
  - exact Q14.
  - exact Q15.
Qed.

Lemma nb_CS_common : forall a W regs regs' mem md md' ly Sa Hp k i1 c j j',
  @ev_CL rc cp PI RL A_prog_listing PA B ARx SK a W regs mem md ly Sa Hp k i1 c j ->
  AJ a ly Sa Hp W mem md' k ->
  (forall r, In r NB_KEPT -> getr regs' r = getr regs r) -> getr regs' 24 = Z_to_bv 64 2147450880 ->
  ev_span a i1 c j' -> (i1 + ev_sg c < j' <= length (ea_x a))%nat ->
  (j' = length (ea_x a) \/ PjGrammar.numch (nth j' (ea_x a) 0) = false) ->
  getr regs' 22 = Z_to_bv 64 (ea_x0 a + Z.of_nat j') ->
  @ev_CS rc cp PI RL A_prog_listing PA B ARx SK a W regs' mem md' ly Sa Hp k i1 c j'.
Proof.
  intros a W regs regs' mem md md' ly Sa Hp k i1 c j j' HCL HJ HK Q24 HSP' Hb' Hst Q22.
  destruct HCL as (HMID & HB & HSC & _ & _ & _ & _ & _ & _ & _ & HFS).
  destruct HB as (HR & R23 & HB').
  destruct HSC as (R27 & V112 & R21 & R11 & R12).
  refine (conj _ (conj _ (conj _ (conj HSP' (conj Hb' (conj Hst (conj _ HFS))))))).
  - split; [exact HJ | exact (proj2 HMID)].
  - split; [|split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23 | exact HB']].
    destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    all: first [ exact Q24 | lazymatch goal with |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption end ].
  - refine (conj _ (conj V112 (conj _ (conj _ _)))).
    all: lazymatch goal with |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption end.
  - rewrite Q22. apply nb_w64. reflexivity.
Qed.

(* ---- the loop statement at a bounded remaining length ---- *)
Definition nb_KLm (a : ev_act) (m : nat) : Prop :=
  forall (fxc : YK11.FPState) W regs mem md ly Sa Hp k i1 c j,
  (length (ea_x a) - j)%nat = m ->
  @ev_pre fx rc cp PI A_prog_listing PA B ARx a -> @ev_fx fx fxc ->
  @ev_CL rc cp PI RL A_prog_listing PA B ARx SK a W regs mem md ly Sa Hp k i1 c j ->
  SRr SEGS W (@ev_cfg rc A_prog_listing PA fxc regs 0x364 mem md) (@ev_to_exit fx rc cp PI RL A_prog_listing PA B ARx SK a).

(* ---- closing a runner pass at a cut: the machine state from the symbolic one by its shape ---- *)
Lemma nb_close_loop : forall a m (fxc : YK11.FPState) W regs mem md ly Sa Hp k i1 c j extra E ss ms md',
  nb_KLm a m -> (length (ea_x a) - j)%nat = S m ->
  @ev_pre fx rc cp PI A_prog_listing PA B ARx a -> @ev_fx fx fxc ->
  @ev_CL rc cp PI RL A_prog_listing PA B ARx SK a W regs mem md ly Sa Hp k i1 c j ->
  @st_ok_pi SEGS VAL fxc E ss (restrict (w_H W) ms) -> nb_shape_loop ss = true ->
  env_agree 32 (Ereg regs extra) E -> ms_mem ms = mem -> AJ a ly Sa Hp W (ms_mem ms) md' k ->
  PjGrammar.numch (nth j (ea_x a) 0) = true -> (S j < length (ea_x a))%nat ->
  SRr SEGS W (mkCfg ms md') (@ev_to_exit fx rc cp PI RL A_prog_listing PA B ARx SK a).
Proof.
  intros a m fxc W regs mem md ly Sa Hp k i1 c j extra E ss ms md' IH Hmj Hpre Hfx HCL HS Hsh HA Hm HJ Hn Hlt.
  unfold nb_shape_loop in Hsh. repeat rewrite andb_true_iff in Hsh.
  destruct Hsh as [[[[[[[[Hpc Hrv] Hkp] S22] S10] S13] S14] S15] S24].
  apply Z.eqb_eq in Hpc.
  assert (Hrv' : ss_resv ss = None) by (unfold nb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv') as Hms.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs extra NB_KEPT HS HA Hkp) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof HCL as (HMID & _ & _ & _ & Hj & R22 & _).
  pose proof HMID as (_ & _ & _ & _ & _ & _ & HSRC & _).
  pose proof HSRC as (_ & Hx0lo & Hx0hi & _).
  pose proof (@alloc_ceiling_value rc) as Hceil.
  destruct HA as [HA0 _].
  assert (E22 : ew E 22 = Z_to_bv 64 (ea_x0 a + Z.of_nat j)).
  { rewrite HA0 by lia. rewrite (ew_Ereg_nat regs extra 22 22%bv eq_refl). exact R22. }
  pose proof (nb_reg_of fxc _ E ss ms 22%bv _ HS S22) as Q22.
  pose proof (nb_reg_of fxc _ E ss ms 10%bv _ HS S10) as Q10.
  pose proof (nb_reg_of fxc _ E ss ms 13%bv _ HS S13) as Q13.
  pose proof (nb_reg_of fxc _ E ss ms 14%bv _ HS S14) as Q14.
  pose proof (nb_reg_of fxc _ E ss ms 15%bv _ HS S15) as Q15.
  pose proof (nb_reg_of fxc _ E ss ms 24%bv _ HS S24) as Q24.
  cbn [sv_denot] in Q22, Q10, Q13, Q14, Q15, Q24.
  rewrite E22, unsigned_lit_small in Q22, Q10 by lia.
  rewrite Hms, Hpc, Hm. rewrite Hm in HJ.
  rewrite <- (nb_cfg fxc (ms_regs ms) 8232 0x364 mem md' eq_refl).
  eapply (IH fxc W (ms_regs ms) mem md' ly Sa Hp k i1 c (S j)); [lia | exact Hpre | exact Hfx |].
  eapply nb_mk_CL; [exact HCL | exact HJ | exact HK | exact Q22 | exact Q10 | exact Q13 | exact Q14 | exact Q15
    | exact Q24 | exact Hn | exact Hlt].
Qed.

Lemma nb_close_stop : forall a (fxc : YK11.FPState) W regs mem md ly Sa Hp k i1 c j extra E ss ms md',
  @KS fx rc cp PI RL A_prog_listing PA B ARx SK a ->
  @ev_pre fx rc cp PI A_prog_listing PA B ARx a -> @ev_fx fx fxc ->
  @ev_CL rc cp PI RL A_prog_listing PA B ARx SK a W regs mem md ly Sa Hp k i1 c j ->
  @st_ok_pi SEGS VAL fxc E ss (restrict (w_H W) ms) -> nb_shape_stop ss = true ->
  env_agree 32 (Ereg regs extra) E -> ms_mem ms = mem -> AJ a ly Sa Hp W (ms_mem ms) md' k ->
  PjGrammar.numch (nth j (ea_x a) 0) = false ->
  SRr SEGS W (mkCfg ms md') (@ev_to_exit fx rc cp PI RL A_prog_listing PA B ARx SK a).
Proof.
  intros a fxc W regs mem md ly Sa Hp k i1 c j extra E ss ms md' HKS Hpre Hfx HCL HS Hsh HA Hm HJ Hn.
  unfold nb_shape_stop in Hsh. repeat rewrite andb_true_iff in Hsh.
  destruct Hsh as [[[[Hpc Hrv] Hkp] S22] S24].
  apply Z.eqb_eq in Hpc.
  assert (Hrv' : ss_resv ss = None) by (unfold nb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv') as Hms.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs extra NB_KEPT HS HA Hkp) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof HCL as (HMID & _ & _ & HSP & Hj & R22 & _).
  destruct HA as [HA0 _].
  pose proof (nb_reg_of fxc _ E ss ms 22%bv _ HS S22) as Q22.
  pose proof (nb_reg_of fxc _ E ss ms 24%bv _ HS S24) as Q24.
  cbn [sv_denot] in Q22, Q24.
  rewrite HA0 in Q22 by lia. rewrite (ew_Ereg_nat regs extra 22 22%bv eq_refl), R22, Z.add_0_r, Z_to_bv_bv_unsigned in Q22.
  rewrite Hms, Hpc, Hm. rewrite Hm in HJ.
  rewrite <- (nb_cfg fxc (ms_regs ms) 9604 0x8c0 mem md' eq_refl).
  eapply (HKS fxc W (ms_regs ms) mem md' ly Sa Hp k i1 c j); [exact Hpre | exact Hfx |].
  eapply nb_CS_common; [exact HCL | exact HJ | exact HK | exact Q24 | exact HSP | | right; exact Hn | exact Q22].
  destruct (Nat.eq_dec j (i1 + ev_sg c)) as [Ej | Nj]; [|lia].
  exfalso. destruct HSP as ((_ & Hd & _) & _). rewrite <- Ej in Hd. rewrite (nb_digit_numch _ Hd) in Hn. discriminate.
Qed.

Lemma nb_close_end : forall a (fxc : YK11.FPState) W regs mem md ly Sa Hp k i1 c j extra E ss ms md',
  @KS fx rc cp PI RL A_prog_listing PA B ARx SK a ->
  @ev_pre fx rc cp PI A_prog_listing PA B ARx a -> @ev_fx fx fxc ->
  @ev_CL rc cp PI RL A_prog_listing PA B ARx SK a W regs mem md ly Sa Hp k i1 c j ->
  @st_ok_pi SEGS VAL fxc E ss (restrict (w_H W) ms) -> nb_shape_end ss = true ->
  env_agree 32 (Ereg regs extra) E -> ms_mem ms = mem -> AJ a ly Sa Hp W (ms_mem ms) md' k ->
  PjGrammar.numch (nth j (ea_x a) 0) = true -> S j = length (ea_x a) ->
  SRr SEGS W (mkCfg ms md') (@ev_to_exit fx rc cp PI RL A_prog_listing PA B ARx SK a).
Proof.
  intros a fxc W regs mem md ly Sa Hp k i1 c j extra E ss ms md' HKS Hpre Hfx HCL HS Hsh HA Hm HJ Hn Hend.
  unfold nb_shape_end in Hsh. repeat rewrite andb_true_iff in Hsh.
  destruct Hsh as [[[[Hpc Hrv] Hkp] S22] S24].
  apply Z.eqb_eq in Hpc.
  assert (Hrv' : ss_resv ss = None) by (unfold nb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv') as Hms.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs extra NB_KEPT HS HA Hkp) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof HCL as (HMID & HB & HSC & HSP & Hj & _).
  pose proof HSC as (_ & _ & _ & _ & R12).
  destruct HA as [HA0 _].
  pose proof (nb_reg_of fxc _ E ss ms 22%bv _ HS S22) as Q22.
  pose proof (nb_reg_of fxc _ E ss ms 24%bv _ HS S24) as Q24.
  cbn [sv_denot] in Q22, Q24.
  rewrite HA0 in Q22 by lia. rewrite (ew_Ereg_nat regs extra 12 12%bv eq_refl), R12, Z.add_0_r, Z_to_bv_bv_unsigned in Q22.
  rewrite Hms, Hpc, Hm. rewrite Hm in HJ.
  rewrite <- (nb_cfg fxc (ms_regs ms) 9604 0x8c0 mem md' eq_refl).
  eapply (HKS fxc W (ms_regs ms) mem md' ly Sa Hp k i1 c (S j)); [exact Hpre | exact Hfx |].
  eapply nb_CS_common; [exact HCL | exact HJ | exact HK | exact Q24 | | lia | left; exact Hend |].
  - destruct HSP as (HLD & HSF). split; [exact HLD|]. apply nb_span_step; [lia | exact HSF | exact Hn].
  - rewrite Q22. unfold ea_len. rewrite <- Hend. reflexivity.
Qed.

(* ---- one iteration: CL at j -> CL at j + 1 (the induction hypothesis) or CS ---- *)
Lemma nb_step : forall a, @KS fx rc cp PI RL A_prog_listing PA B ARx SK a -> forall m, nb_KLm a m -> nb_KLm a (S m).
Proof.
  intros a HKS m IH fxc W regs mem md ly Sa Hp k i1 c j Hmj Hpre Hfx HCL.
  pose proof HCL as (HMID & HB & HSC & HSP & Hj & R22 & R10 & R13 & R14 & R15 & _).
  pose proof HB as (HR & R23 & _).
  pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
  pose proof HSC as (R27 & V112 & R21 & R11 & R12).
  pose proof HMID as (HJ & _ & _ & _ & _ & _ & HSRC & _).
  pose proof HSRC as (HG8 & Hx0lo & Hx0hi & _ & HRA & _).
  pose proof (@alloc_ceiling_value rc) as Hceil.
  assert (Hlen : ea_len a = Z.of_nat (length (ea_x a))) by reflexivity.
  assert (Hjx : (j < length (ea_x a))%nat) by lia.
  destruct (HG8 j Hjx) as [Vb Hb].
  remember (Eimg (PI := PA) (Ereg regs [Z_to_bv 64 (nth j (ea_x a) 0)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (nth j (ea_x a) 0)]) E)
    by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
  { intros n r Hn. subst E. pose proof (u5_range r) as Hr. rewrite Eimg_low by (unfold A_TEXT; lia).
    apply ew_Ereg_nat. exact Hn. }
  assert (E22 : ew E 22 = Z_to_bv 64 (ea_x0 a + Z.of_nat j)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (E12 : ew E 12 = Z_to_bv 64 (ea_x0 a + ea_len a)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (E32 : ew E 32 = Z_to_bv 64 (nth j (ea_x a) 0)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (HS : @st_ok_pi SEGS VAL fxc E NB_ss
     (restrict (w_H W) (@mkst fxc regs (Z_to_bv 64 (BASE + 8232)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold NB_ss. apply pa_entry_st_ok_full.
    - unfold NB_regs.
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; exact R10].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R24].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R15].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R14].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R13].
      subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold NB_mem. constructor; [|constructor]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (ea_x0 a + Z.of_nat j) 0 1%N (SOff 32 0) (nth j (ea_x a) 0)).
      + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      + cbn. lia.
      + rewrite Z.add_0_r. exact Vb.
    - cbn. tauto.
    - split; [|split; exact I]. cbn [NB_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E32, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
  clear HE EE.
  assert (SHOK : sh_ok SEGS NB_Bx [] E (mrestrict (w_H W) mem)) by constructor.
  rewrite (nb_cfg fxc regs 8232 0x364 mem md eq_refl).
  pose proof (@paj_run_x fxc rc SK A_prog_listing PL_prog_A PA B (@prh_pst PI) ARx hl LAWS) as RUN.
  pose proof (@paj_run_to_x fxc rc SK A_prog_listing PL_prog_A PA B (@prh_pst PI) ARx hl LAWS) as RUNTO.
  pose proof (@paj_branch fxc rc A_prog_listing PA) as BR.
  (* +0x364 .. +0x37c: the shadow check of a0 (token, obligation: x[j] addressable), x[j], the digit test *)
  paj_run_tok_x RUN HS HJ SHOK NB_Bspan.
  1: { cbn [ms_mem mkst]. rewrite (U_atom E 22 (ea_x0 a + Z.of_nat j) E22) by lia.
       eapply obl_of_range; [exact HRA | | lia | lia].
       unfold NB_Bx. rewrite U_SLit. apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
  1: { awr_ok_tac. }
  nb_mem mem.
  psrr_branch_tok RUN BR HS SHOK NB_Bspan.
  - (* a digit: +0x394, s6++, a0++, the back edge *)
    cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite E32 in Hc. change (nb_fd (nth j (ea_x a) 0) = true) in Hc.
    assert (Hn : PjGrammar.numch (nth j (ea_x a) 0) = true) by (rewrite (nb_numch _ Hb), Hc; reflexivity).
    clear Hc.
    paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
    psrr_branch_tok RUN BR HS SHOK NB_Bspan;
      cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E22, E12 in Hc; rewrite !unsigned_lit_small in Hc by lia;
      rewrite Z.add_0_r, nb_ltu_lit in Hc by lia.
    + apply Z.ltb_lt in Hc.
      paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan 8232; [awr_ok_tac|]. nb_mem mem.
      lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
        eapply (nb_close_loop a m fxc W regs mem md ly Sa Hp k i1 c j [Z_to_bv 64 (nth j (ea_x a) 0)] E' ss ms _
          IH Hmj Hpre Hfx HCL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
      end.
    + apply Z.ltb_ge in Hc.
      paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan 9604; [awr_ok_tac|]. nb_mem mem.
      lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
        eapply (nb_close_end a fxc W regs mem md ly Sa Hp k i1 c j [Z_to_bv 64 (nth j (ea_x a) 0)] E' ss ms _
          HKS Hpre Hfx HCL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
      end.
  - (* not a digit: the range test b - 43 <= 58 *)
    cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite E32 in Hc. change (nb_fd (nth j (ea_x a) 0) = false) in Hc.
    rename Hc into Hd.
    paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
    psrr_branch_tok RUN BR HS SHOK NB_Bspan;
      cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E32 in Hc.
    + (* out of range: stop at j *)
      change (nb_fr (nth j (ea_x a) 0) = true) in Hc.
      assert (Hn : PjGrammar.numch (nth j (ea_x a) 0) = false) by (rewrite (nb_numch _ Hb), Hd, Hc; reflexivity).
      paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan 9604; [awr_ok_tac|]. nb_mem mem.
      lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
        eapply (nb_close_stop a fxc W regs mem md ly Sa Hp k i1 c j [Z_to_bv 64 (nth j (ea_x a) 0)] E' ss ms _
          HKS Hpre Hfx HCL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn]
      end.
    + (* in range: the mask bit *)
      change (nb_fr (nth j (ea_x a) 0) = false) in Hc. rename Hc into Hr.
      paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
      psrr_branch_tok RUN BR HS SHOK NB_Bspan;
        cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E32 in Hc.
      * (* the bit is clear: stop at j *)
        change (nb_ft (nth j (ea_x a) 0) = true) in Hc.
        assert (Hn : PjGrammar.numch (nth j (ea_x a) 0) = false) by (rewrite (nb_numch _ Hb), Hd, Hr, Hc; reflexivity).
        paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan 9604; [awr_ok_tac|]. nb_mem mem.
        lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
          eapply (nb_close_stop a fxc W regs mem md ly Sa Hp k i1 c j [Z_to_bv 64 (nth j (ea_x a) 0)] E' ss ms _
            HKS Hpre Hfx HCL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn]
        end.
      * (* the bit is set ('+' '-' '.' 'E' 'e'): +0x394 and the back edge *)
        change (nb_ft (nth j (ea_x a) 0) = false) in Hc.
        assert (Hn : PjGrammar.numch (nth j (ea_x a) 0) = true) by (rewrite (nb_numch _ Hb), Hd, Hr, Hc; reflexivity).
        clear Hc.
        paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
        psrr_branch_tok RUN BR HS SHOK NB_Bspan;
          cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E22, E12 in Hc; rewrite !unsigned_lit_small in Hc by lia;
          rewrite Z.add_0_r, nb_ltu_lit in Hc by lia.
        -- apply Z.ltb_lt in Hc.
           paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan 8232; [awr_ok_tac|]. nb_mem mem.
           lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
             eapply (nb_close_loop a m fxc W regs mem md ly Sa Hp k i1 c j [Z_to_bv 64 (nth j (ea_x a) 0)] E' ss ms _
               IH Hmj Hpre Hfx HCL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
           end.
        -- apply Z.ltb_ge in Hc.
           paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan 9604; [awr_ok_tac|]. nb_mem mem.
           lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
             eapply (nb_close_end a fxc W regs mem md ly Sa Hp k i1 c j [Z_to_bv 64 (nth j (ea_x a) 0)] E' ss ms _
               HKS Hpre Hfx HCL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
           end.
Qed.

Lemma nb_base : forall a, nb_KLm a 0.
Proof. intros a fxc W regs mem md ly Sa Hp k i1 c j Hmj Hpre Hfx HCL. exfalso. destruct HCL as (_ & _ & _ & _ & Hj & _). lia. Qed.

Lemma nb_all : forall a, @KS fx rc cp PI RL A_prog_listing PA B ARx SK a -> forall m, nb_KLm a m.
Proof. intros a HKS m. induction m as [|m IHm]; [apply nb_base | exact (nb_step a HKS m IHm)]. Qed.

(* sub-piece B: CL -> CS (S8aNumCut.v ev_B_stmt) *)
Theorem ev_B : @ev_B_stmt fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof.
  intros a HKS fxc W regs mem md ly Sa Hp k i1 c j Hpre Hfx HCL.
  exact (nb_all a HKS _ fxc W regs mem md ly Sa Hp k i1 c j eq_refl Hpre Hfx HCL).
Qed.
End d.
