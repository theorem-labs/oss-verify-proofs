(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths changed; 148 of its 197 lines of code are new or changed and 541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Dig.v, with its module paths changed; 287 of its 323 lines of code are new or changed and 161 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0DigW.v at 97ea9c9eafa (its engine states, the
   byte read-back dg_bytes_of_st, dg_all / dg_upto, dg_frame, dg_awr_frame, dg_sh_bounds and its runs 1 and 3) and
   proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 97ea9c9eafa (o_reg, o_notin, o_keep, o_agree_atom as dg_reg,
   dg_notin, dg_keep, dg_agree_atom); re-walked on image B's own code (pcs, registers, the frame of class 4 with 128
   shadow bytes, image B's shadow base s11), the register-kept lemma taken from lib/AU/HPgSteps.v and the allocator
   laws from the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the kit of the walk of the
   DIG block of ent_build's case 0 (pod.h:237-246) in LLVMFuzzerTestOneInput 0x80c40, from DIG 0x81a1c to
   G 0x81afc, and its two shadow-store runs. Proves no function (kind: segment lemma).

   THE CODE (image B) and how the walk cuts it:
     1  0x81a1c .. 0x81a2c  a2 := 0, a6 := a3 & 63 (a3 = c), `sb t0,0x1c(s3)` (t0 = 4: r in scope), a1 := a7 := s6
     2  0x81a30 .. 0x81af4  the digit loop (the UBSan test `bne a2,t0`, the shadow check of r[a2] with its slow
                            block 0x81a8c, the `% 10` by `mulhu` with s8 and `mul` by t2, the store of the digit,
                            `bltu t3,a5`), the reverse loop (the shadow check of r[a0], slow block 0x81ad0, `lbu` from
                            r, `sb` into ch), the digit count n into a0, `ld a1,0xc0(s1)` (= ~&ch), the UBSan test
                            `bgeu a1,a0`, the NUL at ch[n]
     3  0x81af8             `sb s7,0x1c(s3)` (s7 = -8: r out of scope again)
   Runs 1 and 3 store a shadow byte, so they are plain engine runs (YCbq.v aj_run_to) with that byte (granule 0x1c
   of s3 = shadow_addr F) as their only region. Run 2 (lib/AU/HPgE0DigR.v) passes instrumented checks, so it is a
   token run (aj_run_to_tok) with the frame's shadow row out of the state.
   Registers used: s3 (19) = shadow_addr F, s6 (22) = &r = F+0xe0, s2 (18) = &ch = F+0xa0, s11 (27) = K, s1 (9) = R,
   s8 (24) = HSU_MULT10, t0 (5) = 4, t3 (28) = 9, t2 (7) = 10, s7 (23) = -8, a3 (13) = c; the R-cell R+0xc0 = ~&ch.
   The block changes a0 .. a7 only. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgMem HPgSeg HPgE0Def HPgE0Base HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the constants and the engine states ---- *)
(* the highest address a frame for locals reaches (alloc_ceiling's bound, YCbq.v asan_consts) *)
Definition DG_FHI : Z := 0x7fffff800000.
(* the range of R+0xc0 = ~&ch = 2^64 - (F + 0xa0) - 1 over every frame for locals F in [4096, DG_FHI) *)
Definition DG_KLO : Z := 2 ^ 64 - DG_FHI - 0xa1.
Definition DG_KHI : Z := 2 ^ 64 - 4096 - 0xa1.
(* run 2: r[4] (s6 = F + 0xe0) and ch[24] (s2 = F + 0xa0), both writable and 32-aligned, and the cell R+0xc0
   (s1 = R) read-only, its value the fresh atom 32 with the range above *)
Definition dg_regions : smem :=
  [ YP09.mkRegion (Some 22%nat) 0 4 0 4 []; YP09.mkRegion (Some 18%nat) 0 24 0 24 [];
    YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0 0 [YP09.mkChunk 0xc0 (CVal 8 (SOff 32 0))] ].
Definition dg_facts : facts := mkFacts
  [ (27%nat, mkAF E0SB E0SB 0); (22%nat, mkAF 4096 DG_FHI 5); (18%nat, mkAF 4096 DG_FHI 5);
    (32%nat, mkAF DG_KLO DG_KHI 0) ] [] [].
Definition ss_dg2 : sstate := mkSS 0x81a30 sr_atoms dg_regions None dg_facts.
(* the two writable windows lie in application memory (empty entries: no shadow fact is assumed) *)
Definition dg_SH : list shent := [mkSHE 22 4 0; mkSHE 18 24 0].
(* runs 1 and 3: the frame's shadow byte of r (granule 0x1c from s3 = shadow_addr F) *)
Definition ss_dgr (pc : Z) : sstate :=
  mkSS pc sr_atoms [YP09.mkRegion (Some 19%nat) 0x1c 0x1d 0x1c 0x1d []] None (mkFacts [] [] []).
(* what the block may change *)
Definition dg_clob : list (bv 5) := [10; 11; 12; 13; 14; 15; 16; 17]%bv.
Definition dg_wr (F : Z) : Z -> Prop :=
  fun a => (F + 0xa0 <= a < F + 0xb8) \/ (F + 0xe0 <= a < F + 0xe4) \/ a = shadow_addr F + 0x1c.
(* HPgE0Def.e0_tbl, computed once *)
Definition dg_tbl : ctable := Eval vm_compute in e0_tbl.
Lemma dg_tbl_ok : table_ok rsegs dg_tbl.
Proof.
assert (E : e0_tbl = dg_tbl) by (vm_compute; reflexivity). rewrite <- E. exact e0_tbl_ok.
Qed.

(* ---- reading literal bytes back out of a region's chunks ---- *)
Definition dg_lb (z : Z) : Z := bv_unsigned (YP09.byte_of_word (Z_to_bv 64 z) 0).
Definition dg_ck (o b : Z) (ck : YP09.chunk) : bool :=
  (YP09.c_off ck =? o) &&
  match YP09.c_val ck with CVal w (SLit z) => N.eqb w 1 && (dg_lb z =? b) | _ => false end.
Definition dg_has (cs : list YP09.chunk) (o0 : Z) (l : list byte) : bool :=
  forallb (fun i => existsb (dg_ck (o0 + Z.of_nat i) (bv_unsigned (nth i l (Z_to_bv 8 0)))) cs) (seq 0 (length l)).
Definition dg_reg_has (orr : option YP09.region) (k : nat) (o0 : Z) (l : list byte) : bool :=
  match orr with
  | Some r => match YP09.r_base r with Some k' => Nat.eqb k' k && dg_has (YP09.r_chunks r) o0 l | None => false end
  | None => false
  end.

(* every v in [0, n) from one goal per literal *)
Fixpoint dg_all (P : Z -> Prop) (n : nat) : Prop :=
  match n with O => True | S n' => dg_all P n' /\ P (Z.of_nat n') end.
Lemma dg_upto : forall (P : Z -> Prop) n, dg_all P n -> forall v, 0 <= v < Z.of_nat n -> P v.
Proof.
intros P n. induction n as [|n IH]; intros H v Hv; [lia|].
destruct H as [H1 H2]. destruct (Z.eq_dec v (Z.of_nat n)) as [->|Hne]; [exact H2|].
apply IH; [exact H1 | lia].
Qed.

(* ---- tactics ---- *)
(* the value of register r at a run's last state *)
Ltac dg_reg HS r :=
rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS);
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end.
(* a register outside a concrete clobber list *)
Ltac dg_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac dg_keep Hk := rewrite Hk by first [cbv; discriminate | dg_notin].
(* the I/O state across a run: the run's model is the entry's, possibly with its vm backing set *)
Ltac dg_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma dg_bytes_of_st : forall E ss (H : word -> bool) ms i (k : nat) b o0 (l : list byte),
st_ok rsegs E ss (restrict H ms) -> dg_reg_has (nth_error (ss_mem ss) i) k o0 l = true ->
bv_unsigned (ew E k) = b -> hm_bytes rsegs H (ms_mem ms) (b + o0) l.
Proof.
intros E ss H ms i k b o0 l HS Hc Hb.
unfold dg_reg_has in Hc. destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hn; [|discriminate].
destruct (YP09.r_base r) as [k'|] eqn:Hbase; [|discriminate].
apply andb_prop in Hc as [Hk Hc]. apply Nat.eqb_eq in Hk. subst k'.
pose proof (st_ok_region_at E ss (restrict H ms) i r HS Hn) as Hok.
destruct Hok as (_ & _ & _ & Hcs).
apply hm_bytes_aview. intros j Hj.
unfold dg_has in Hc. rewrite forallb_forall in Hc.
specialize (Hc j ltac:(apply in_seq; lia)). apply existsb_exists in Hc as (ck & Hin & Hck).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hok. rewrite Hbase in Hok. cbn [base_val] in Hok. rewrite Hb in Hok.
destruct ck as [off cv]. unfold dg_ck in Hck. cbn [YP09.c_off YP09.c_val] in Hck, Hok.
apply andb_prop in Hck as [Ho Hv]. apply Z.eqb_eq in Ho.
destruct cv as [w e | | |]; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hv as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w off.
destruct (Hok 0 ltac:(cbn; lia)) as (bt & E1 & E2).
cbn [YP09.cbyte YP09.c_off YP09.c_val sv_denot] in E1, E2. injection E1 as <-.
unfold aview. replace (b + o0 + Z.of_nat j) with (b + (o0 + Z.of_nat j) + 0) by lia.
change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in E2.
rewrite E2. cbn [option_map]. f_equal. exact Hz.
Qed.

(* an atom below 32 of a run's last environment is the register it started as *)
Lemma dg_agree_atom : forall regs extra Ev n (r : bv 5), env_agree 32 (Ereg regs extra) Ev -> (n < 32)%nat ->
Z.of_nat n = bv_unsigned r -> sv_denot Ev (SOff n 0) = getr regs r.
Proof.
intros regs extra Ev n r [HA _] Hn Hr. apply bv_eq.
rewrite denot_SOff, (HA n Hn), (ew_Ereg_nat regs extra n r Hr), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.

(* a token run's last environment agrees with its first below 32: it only sets the fresh atoms K, K + 1, ... *)
Lemma dg_agree_step : forall E0 E k w, env_agree 32 E0 E -> (32 <= k)%nat -> env_agree 32 E0 (ewset E k w).
Proof.
intros E0 E k w [HA HD] Hk. split; [|exact HD].
intros n Hn. rewrite ew_ewset_other by lia. exact (HA n Hn).
Qed.

Lemma dg_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F H. apply Z.mod_divide in H; [|lia]. destruct H as [z Hz]. rewrite Hz.
replace (z * 32) with ((4 * z) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma dg_sh_bounds : forall F, 4096 <= F -> F + 1024 <= DG_FHI ->
SHADOW_OFF + 512 <= shadow_addr F /\ shadow_addr F + 128 <= SHADOW_OFF + 2 ^ 44.
Proof.
intros F H0 H1. unfold shadow_addr, SHADOW_OFF, DG_FHI in *.
assert (D0 : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (D1 : F / 8 <= 17592186044288) by (apply Z.div_le_upper_bound; lia).
change (2 ^ 44) with 17592186044416. lia.
Qed.

(* the value of the R-cell R+0xc0, as an unsigned word *)
Lemma dg_kval : forall F, 4096 <= F -> F + 1024 <= DG_FHI ->
(- F - 0xa0 - 1) mod 2 ^ 64 = 2 ^ 64 - F - 0xa1 /\ DG_KLO <= 2 ^ 64 - F - 0xa1 <= DG_KHI.
Proof.
intros F H0 H1. split.
- symmetry. apply (Z.mod_unique _ _ (-1)); [left; unfold DG_FHI in *; lia | lia].
- unfold DG_KLO, DG_KHI, DG_FHI in *. lia.
Qed.

(* an application byte is not the frame's shadow byte of r *)
Lemma dg_app_not_sh : forall lo len a F, in_app lo len -> lo <= a < lo + len -> 4096 <= F -> F + 1024 <= DG_FHI ->
a <> shadow_addr F + 0x1c.
Proof.
intros lo len a F Happ Ha HF0 HF1 Heq. pose proof (dg_sh_bounds F HF0 HF1) as (SB0 & SB1).
revert SB0 SB1 Happ Ha Heq. unfold SHADOW_OFF. generalize (shadow_addr F). intros s SB0 SB1 Happ Ha Heq.
change (2 ^ 44) with 17592186044416 in SB1. zlia.
Qed.
(* an application byte is not a byte of the frame's shadow row *)
Lemma dg_app_not_shr : forall lo len a F, in_app lo len -> lo <= a < lo + len -> 4096 <= F -> F + 1024 <= DG_FHI ->
~ (shadow_addr F <= a < shadow_addr F + 128).
Proof.
intros lo len a F Happ Ha HF0 HF1 X. pose proof (dg_sh_bounds F HF0 HF1) as (SB0 & SB1).
revert SB0 SB1 Happ Ha X. unfold SHADOW_OFF. generalize (shadow_addr F). intros s SB0 SB1 Happ Ha X.
change (2 ^ 44) with 17592186044416 in SB1. zlia.
Qed.

(* a register the block keeps: x1 .. x9 and x18 .. x31 are outside dg_clob *)
Lemma dg_kept_reg : forall (regs regs' : bvmap 5 word),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r dg_clob -> getr regs' r = getr regs r) ->
forall q, (1 <= q <= 9 \/ 18 <= q <= 31) -> getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q).
Proof.
intros regs regs' Hk q Hq.
assert (Hu : bv_unsigned (Z_to_bv 5 q) = q).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
apply Hk.
- rewrite Hu. lia.
- intros Hin. unfold dg_clob in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal (@bv_unsigned 5)) in Hin; rewrite Hu in Hin;
    vm_compute in Hin; lia|]).
  exact Hin.
Qed.

Section d.
Variable B : asyms.

(* the frame for locals of the block's journal: 32-aligned, its bytes and its shadow bytes present *)
Lemma dg_frame : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
F mod 32 = 0 /\ 4096 <= F /\ F + 1024 <= DG_FHI /\ in_app F 1024 /\
(forall a, F <= a < F + 1024 -> apresent (w_H W) memc a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W) memc (shadow_addr F + i)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & HFapp & HFpres & HFsh).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- HF in HF32, HFapp, HFpres, HFsh, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in HFapp, HFpres, HFsh, HFceil.
pose proof asan_consts as (C1 & _).
split; [exact HF32|]. split; [exact HF4096|]. split; [unfold DG_FHI; lia|]. split; [exact HFapp|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
intros i Hi. exact (proj1 (HFsh i ltac:(change (1024 / 8) with 128; lia))).
Qed.

(* an awr_ok window inside the frame for locals or its shadow row *)
Lemma dg_awr_frame : forall STK sp0 FP bl0 blc lyc own F pos a,
In (4, pos) own -> F = frame_addr lyc 4 pos ->
(F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) ->
awr_byte STK sp0 FP bl0 blc lyc own a.
Proof.
intros STK sp0 FP bl0 blc lyc own F pos a Hown HF Ha.
right; right; right. exists 4, pos. split; [exact Hown|]. unfold in_zr. cbn [fst snd]. rewrite <- HF.
change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

(* the frame for locals lies below the allocator's ceiling *)
Lemma dg_frame_ceil : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos -> F + 1024 <= alloc_ceiling.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & HFceil & _).
rewrite <- HF in HFceil. change (fs_frame_bytes 4) with 1024 in HFceil. exact HFceil.
Qed.

(* ======================== run 1: DIG 0x81a1c -> 0x81a30 ======================== *)
Lemma dg_run1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) F pos c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 13 = w64 c -> getr regs 5 = w64 4 ->
getr regs 22 = w64 (F + 0xe0) -> 0 <= c < 256 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 E0_DIG) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81a30 regs memc mdc [11; 12; 16; 17]%bv
  (fun a => a = shadow_addr F + 0x1c)
  (fun regs2 mem2 => getr regs2 12 = w64 0 /\ getr regs2 16 = w64 (c mod 64) /\
     getr regs2 11 = w64 (F + 0xe0) /\ getr regs2 17 = w64 (F + 0xe0) /\
     aview rsegs (w_H W) mem2 (shadow_addr F + 0x1c) = Some 4)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs F pos c HJ Hown HF H19 H13 H5 H22 Hc.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct (dg_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & HFpres & HFsh).
pose proof (dg_sh_bounds F HF4096 HFhi) as (SB0 & SB1).
assert (B19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F)
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (E13 : ew (Ereg regs []) 13 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E22 : ew (Ereg regs []) 22 = Z_to_bv 64 (F + 0xe0)) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (HS0 : st_ok rsegs (Ereg regs []) (ss_dgr E0_DIG)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 E0_DIG) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ (w_H W) memc 19%nat (shadow_addr F) 0x1c 0x1d 0x1c 0x1d []);
      [exact B19 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ 5%bv 4 HS0 eq_refl H5) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_dgr] in HS. clear HS0.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to dg_tbl_ok HS HJ 0x81a30.
- eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact B19 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). right. lia.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | dg_io | | | exact HG | ].
  + eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((5%bv : bv 5), SLit 4)] HS);
      [ exact HAE
      | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst; cbn [sv_denot]; exact (eq_sym H5)
      | vm_compute; reflexivity ].
  + intros a Ha Hz. eapply (cb_kept_run (fun a => a = shadow_addr F + 0x1c) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ | exact Ha | exact Hz].
    intros x (r & Hr & Hb). cbn [In] in Hr. destruct Hr as [<-|[]].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite B19 in Hb. lia.
  + split; [|split; [|split; [|split]]].
    * dg_reg HS (12%bv : bv 5). reflexivity.
    * dg_reg HS (16%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
      rewrite U_SAlu, U_SLit, (U_atom _ 13 c E13) by lia. cbn [zalu_raw].
      change (zcanon 63) with 63.
      replace (Z.land c 63) with (c mod 64) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
      apply zcanon_id. pose proof (Z.mod_pos_bound c 64 ltac:(lia)). unfold M64. lia.
    * dg_reg HS (11%bv : bv 5). rewrite (dg_agree_atom regs [] _ 22 22%bv HAE ltac:(lia) eq_refl). exact H22.
    * dg_reg HS (17%bv : bv 5). rewrite (dg_agree_atom regs [] _ 22 22%bv HAE ltac:(lia) eq_refl). exact H22.
    * pose proof (dg_bytes_of_st _ _ (w_H W) ms 0 19 (shadow_addr F) 0x1c [Z_to_bv 8 4] HS
        ltac:(vm_compute; reflexivity) B19) as Hb.
      pose proof (proj1 (hm_bytes_aview rsegs _ _ _ _) Hb 0%nat ltac:(cbn; lia)) as Ha.
      rewrite Z.add_0_r in Ha. exact Ha.
Qed.

(* ======================== run 3: 0x81af8 -> G 0x81afc ======================== *)
Lemma dg_run3 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 23 = w64 (-8) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81af8) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81afc regs memc mdc []
  (fun a => a = shadow_addr F + 0x1c)
  (fun _ mem2 => aview rsegs (w_H W) mem2 (shadow_addr F + 0x1c) = Some 0xf8)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs F pos HJ Hown HF H19 H23.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct (dg_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & HFpres & HFsh).
pose proof (dg_sh_bounds F HF4096 HFhi) as (SB0 & SB1).
assert (B19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F)
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (HS0 : st_ok rsegs (Ereg regs []) (ss_dgr 0x81af8)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81af8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ (w_H W) memc 19%nat (shadow_addr F) 0x1c 0x1d 0x1c 0x1d []);
      [exact B19 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ 23%bv (-8) HS0 eq_refl H23) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_dgr] in HS. clear HS0.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to dg_tbl_ok HS HJ 0x81afc.
- eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact B19 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). right. lia.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | dg_io | | | exact HG | ].
  + eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((23%bv : bv 5), SLit (-8))] HS);
      [ exact HAE
      | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst; cbn [sv_denot]; exact (eq_sym H23)
      | vm_compute; reflexivity ].
  + intros a Ha Hz. eapply (cb_kept_run (fun a => a = shadow_addr F + 0x1c) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ | exact Ha | exact Hz].
    intros x (r & Hr & Hb). cbn [In] in Hr. destruct Hr as [<-|[]].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite B19 in Hb. lia.
  + pose proof (dg_bytes_of_st _ _ (w_H W) ms 0 19 (shadow_addr F) 0x1c [Z_to_bv 8 0xf8] HS
      ltac:(vm_compute; reflexivity) B19) as Hb.
    pose proof (proj1 (hm_bytes_aview rsegs _ _ _ _) Hb 0%nat ltac:(cbn; lia)) as Ha.
    rewrite Z.add_0_r in Ha. exact Ha.
Qed.
End d.
End b.

Print Assumptions dg_tbl_ok.
Print Assumptions dg_bytes_of_st.
Print Assumptions dg_frame.
Print Assumptions dg_run1.
Print Assumptions dg_run3.
