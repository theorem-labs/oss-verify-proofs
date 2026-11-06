(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_add on fuzz_command.asan-ubsan (image B): the B
   re-walk of lib/A/Prog/descriptors_add.v (a working branch 9a46e579716), in the shape of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment through a program call and back) and of this harness's
   B walk lib/B/Prog/rec_clear.v (a working branch). A inlines record() and xstrdup; B calls record and
   arg_s, so the walk is four straight-line segments joined by three program calls.

   descriptors_add (BASE + AF_descriptors_add = 0x8cc54, 20 instructions, 80 bytes; measured on
   fuzz_command.asan-ubsan, sha256 658cefbe..., with capstone, keyed by .symtab): no branch, no inline ASan check,
   no call of an __asan_report_* entry, no UBSan trap site. So the walk has one path and no report or trap edge.
     0x8cc54 .. 0x8cc6c  the 32-byte frame (ra, s0, s1), s0 := uri, a0 := 22, jal record (0x8a728)
     0x8cc70 .. 0x8cc78  s1 := the slot, a1 := uri, jal arg_s (0x8a820)
     0x8cc7c .. 0x8cc88  s0 := 0x5e3c7c (auipc), a0 := g_rec.state, a1 := the slot, jal mix_call (0x8ad54)
     0x8cc8c .. 0x8cca0  g_rec.state := a0 (sd a0, -0x60c(s0)), the frame popped, ret
   The segment states, their runs and their state checks are lib/B/Prog/descriptors_add_aux.v.

   Section hypotheses: the statement's own (TRECORD, TARG_S, TMIX_CALL at every FP state, VOBJS; a Theorem Labs lane
   707acd856cb); HB and MTL; and, in the convention of the B walks (a Theorem Labs lane, 09:0xZ), a Theorem Labs lane's record facts
   (a working branch 707acd856cb lib/B/Prog/CmdRec*.v, RecBLemmas.v) used by exact over any image from ONE
   pinned hypothesis cmd_img_facts_tfib (CmdRecImg.v) and CmdRecCells.v's premise PRW (the core's prog_rw); the
   facts a Theorem Labs lane states at the concrete instance only (CmdRecRest.v) are Section hypotheses under the lemma's name:
   cmd_val_his_PB (the store at 0x8cc8c goes through pa_val (A_HI 203)) and cmd_sig_prog_PB. The closing file
   DescriptorsAddClosed.v discharges them at PB_cmd. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibG PaLibH PaLibF
PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c mix_call_c descriptors_add_c descriptors_add_aux RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRo CmdRecCells CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* --- the program's statics, the call's footprint, the slot ------------------------------------------------ *)
(* the program's writable statics are RecBLemmas' recb_PG (g_rec, record.spill, g_quitting) *)
Lemma dab_PG_range : forall a, Exists (in_zr a) recb_PG -> A_G_REC <= a < A_G_QUITTING + 4.
Proof.
intros a H. apply Exists_exists in H as ([b n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
unfold recb_PG in Hin. destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <-;
unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in *; lia.
Qed.
(* the footprint the statement names: g_rec, record.spill and the recorder's blocks *)
Definition dab_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the registers every callee and every segment keeps: gp, tp, s2 .. s11 *)
Definition dab_keep_r (r : bv 5) : Prop := bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ 18 <= bv_unsigned r <= 27.
Definition dab_keep (regs regs' : bvmap 5 word) : Prop := forall r : bv 5, dab_keep_r r -> getr regs' r = getr regs r.
Lemma dab_keep_trans : forall r1 r2 r3, dab_keep r1 r2 -> dab_keep r2 r3 -> dab_keep r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma dab_bv5_id : forall r : bv 5, Z_to_bv 5 (bv_unsigned r) = r.
Proof.
intros r. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. apply bv_unsigned_in_range.
Qed.
Lemma dab_pres_bv : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H (bv_unsigned r) Hr) as X. rewrite !dab_bv5_id in X. exact X. Qed.
Lemma dab_keep_pres : forall r1 r2, aregs_preserved r1 r2 -> dab_keep r1 r2.
Proof. intros r1 r2 H r Hr. apply dab_pres_bv; [exact H|]. unfold dab_keep_r, acallee_saved in *. lia. Qed.
Definition dab_keep_list : list (bv 5) := map (Z_to_bv 5) [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma dab_keep_in : forall r : bv 5, dab_keep_r r -> In r dab_keep_list.
Proof.
intros r Hr. rewrite <- (dab_bv5_id r). unfold dab_keep_list. apply in_map. unfold dab_keep_r in Hr.
assert (Hk : bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/
  bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/
  bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
clear Hr. repeat (destruct Hk as [Hk | Hk]; [rewrite Hk; repeat (first [left; reflexivity | right]) |]).
rewrite Hk. repeat (first [left; reflexivity | right]).
Qed.

(* the slot record() returns *)
Lemma dab_slot_cases : forall R,
((length (r_calls R) < 16)%nat /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) \/
((16 <= length (r_calls R))%nat /\ rec_slot R = A_REC_SPILL).
Proof.
intros R. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H | H]; [left | right]; split; auto.
Qed.
Lemma dab_slot_mix : forall R,
(exists i, 0 <= i < REC_CALLS_MAX /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ rec_slot R = A_REC_SPILL.
Proof.
intros R. destruct (dab_slot_cases R) as [(H & E) | (_ & E)]; [left | right; exact E].
exists (Z.of_nat (length (r_calls R))). unfold REC_CALLS_MAX. split; [lia | exact E].
Qed.
Lemma dab_slot_in : forall R o, 0 <= o < CALL_SIZE ->
(A_G_REC + OFF_CALLS <= rec_slot R + o < A_G_REC + OFF_STATE) \/ (A_REC_SPILL <= rec_slot R + o < A_REC_SPILL + SC_SIZE).
Proof.
intros R o Ho. destruct (dab_slot_cases R) as [(H & E) | (_ & E)]; rewrite E; [left | right];
unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_STATE, CALL_SIZE, SC_SIZE in *; lia.
Qed.
Lemma dab_slot_PG : forall R o, 0 <= o < CALL_SIZE ->
Exists (in_zr (rec_slot R + o)) recb_PG /\ ~ (A_G_QUITTING <= rec_slot R + o < A_G_QUITTING + 4) /\
A_G_REC <= rec_slot R + o < A_REC_SPILL + SC_SIZE.
Proof.
intros R o Ho. destruct (dab_slot_in R o Ho) as [H | H].
- split; [apply recb_grec_in; unfold A_G_REC, OFF_CALLS, OFF_STATE, REC_SIZE in *; lia|].
  unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_CALLS, OFF_STATE, SC_SIZE in *. lia.
- split; [apply recb_spill_in; exact H|].
  unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_CALLS, OFF_STATE, SC_SIZE in *. lia.
Qed.

(* --- the allocator's blocks ------------------------------------------------------------------------------- *)
Lemma dab_pw_in : forall (f : Z * Z -> Z * Z) (l : list (Z * Z)) b1 b2,
pairwise zdisjoint (map f l) -> In b1 l -> In b2 l -> b1 <> b2 -> zdisjoint (f b1) (f b2).
Proof.
intros f l. induction l as [|y l IH]; intros b1 b2 Hp H1 H2 Hne; [destruct H1|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf.
destruct H1 as [<- | H1]; destruct H2 as [<- | H2].
- exfalso. exact (Hne eq_refl).
- exact (Hf (f b2) (in_map f l b2 H2)).
- pose proof (Hf (f b1) (in_map f l b1 H1)) as Hd. unfold zdisjoint in *. lia.
- exact (IH b1 b2 Hp H1 H2 Hne).
Qed.

(* --- the recorder's representation ------------------------------------------------------------------------- *)
Lemma dab_rep_blocks : forall B ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros B ly S rd R O (Q & HA & HOQ) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HA pn (proj1 (HOQ pn) Hpn)).
Qed.
(* a reader that agrees everywhere keeps the representation *)
Lemma dab_rep_same : forall B ly S (rd rd' : reader) R O, rec_repA B ly S rd R O ->
(forall a, rd' a = rd a) -> rec_repA B ly S rd' R O.
Proof.
intros B ly S rd rd' R O (Q & HA & HOQ) K. exists Q. split; [|exact HOQ].
apply (dab_arep_kept (ablocks B ly S) (ablocks B ly S) rd rd' R Q HA).
- intros a _. apply K.
- intros pn i _ _. apply K.
- exact (lay_blocks_in _ _ _ _ _ _ HA).
Qed.
(* the call the recorder holds in the slot record() returned *)
Lemma dab_acall_slot : forall bl rd R fn A Q,
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) Q -> exists P, acall_at bl rd (rec_slot R) (fn, A) P.
Proof.
intros bl rd R fn A Q (_ & _ & _ & HC & _).
destruct HC as (_ & HlQ & _ & HCi & HSp & _).
unfold rec_slot. unfold rec_record in *.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge].
- cbn [set_calls r_calls] in HlQ, HCi.
  assert (Hc : nth_error (r_calls R ++ [(fn, A)]) (length (r_calls R)) = Some (fn, A))
    by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
  assert (HlQ' : (length (r_calls R) < length (l_calls Q))%nat) by (rewrite HlQ, length_app; cbn; lia).
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:EP;
  [|apply nth_error_None in EP; lia].
  exists P. exact (proj1 (HCi _ _ _ Hc EP)).
- cbn [set_spill r_spill] in HSp. exists (l_spill Q). exact HSp.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation STK := DESCRIPTORS_ADD_STK.
(* the statement's own hypotheses (descriptors_add_c.v:64-67): the callees' contracts at every FP state *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the facts a Theorem Labs lane states at the concrete instance only (CmdRecRest.v, PI := PB_cmd), here over the abstract PI
   and under the lemma's name: the values of the listing's auipc atoms (the store at 0x8cc8c goes through
   pa_val (A_HI 203)) and the call targets of the program functions *)
Hypothesis cmd_val_his_PB : cmd_val_his.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the per-binary record and the meter laws, and the premises of a Theorem Labs lane's record facts over any image *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the image facts at the image: a Theorem Labs lane's pinned lemma CmdRecImg.cmd_img_facts_tfib, discharged by exact *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @CmdRecBase.cmd_img_facts SK SEGS B0.
(* the writability of the program's statics: CmdRecCells.v's own premise PRW (the core's prog_rw, YCbq.v:1145) *)
Hypothesis PRW : prog_rw SEGS B.

Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @CmdRecBase.cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let RUNP := SRr_run_pi_AJ (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PL := PL_cmd) (PI := PI) B LAWS.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma dab_STK : STK = 16592.
Proof. reflexivity. Qed.
(* a Theorem Labs lane's record facts over any image (a working branch 707acd856cb), used by exact *)
Lemma dab_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a.
Proof. exact (CmdRecRest.cmd_prog_img SEGS B LAWS HB IMG). Qed.
Lemma dab_ro_prog_apart : forall a, in_roP SEGS CMD_RLO CMD_RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC.
Proof. exact (CmdRecRest.cmd_ro_prog_apart SEGS B LAWS HB IMG). Qed.
Lemma dab_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS CMD_RLO CMD_RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Proof. exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG). Qed.
Lemma dab_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e.
Proof. exact (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB). Qed.
Lemma dab_prog_writable : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a.
Proof. exact (CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW). Qed.

(* the post-condition of the statement (descriptors_add_c.v:92-103) *)
Definition dab_Q (ly : alayout) (S : astate) (R : rstate) (uri : option (list byte)) (O : list (Z * Z))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (descriptors_add_m R uri) O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_DESCRIPTORS_ADD uri /\
 mo_le MT S S' (XM_DESCRIPTORS_ADD MT R uri).

(* a write of this call to g_rec or record.spill is one the journal admits (awr_byte's program-static disjunct,
   lib/Reusable/YCbq.v), and so is a write into a block of the recorder's O that is live at the call *)
Lemma dab_awr_PG : forall STK0 sp0 O bl0 blc fr0 lyx own a,
Exists (in_zr a) recb_PG -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) ->
awr_byte SEGS B STK0 sp0 (dab_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK0 sp0 O bl0 blc fr0 lyx own a Ha Hq. right; right; right; right. left.
split; [| split; [rewrite (recb_ts_prog_m B HB); exact Ha | exact (dab_prog_img a Ha)]].
pose proof Ha as Ha'. apply Exists_exists in Ha' as ([b n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
unfold recb_PG in Hin. destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <-.
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
- exfalso. lia.
Qed.
Lemma dab_awr_blk : forall STK0 sp0 O bl0 blc fr0 lyx own p n a, In (p, n) O -> In (p, n) blc -> p <= a < p + req_size n ->
awr_byte SEGS B STK0 sp0 (dab_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK0 sp0 O bl0 blc fr0 lyx own p n a HO Hb Ha. right; left. split.
- exists (p, p + req_size n). split; [|cbn [fst snd]; lia].
  right; right. unfold ablocks_fp. apply in_map_iff. exists (p, n). split; [reflexivity | exact HO].
- exists p, n. split; [exact Hb | exact Ha].
Qed.

(* the facts the allocator law gives on a block: below the ceiling, apart from the image *)
Lemma dab_blk : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n /\ 1 <= req_size n /\ n <= req_size n /\
(p + req_size n <= 0x10000 \/ 0x606000 <= p).
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [H1 H2].
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
repeat split; lia.
Qed.
Lemma dab_ceil : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.

(* the footprint is closed (no sink token), and the read-only range is off it *)
Lemma dab_FP_closed : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> ~ YI16.sink_open_fp (dab_FP O).
Proof.
intros ly S W mem md O HAR HO. apply sink_closed_pos.
constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hin. cbn [fst].
pose proof (dab_blk ly S W mem md p n HAR (HO _ Hin)). lia.
Qed.
Lemma dab_ro_off_FP : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, in_roP SEGS RLO RHI a -> ~ inFP (dab_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro (r & Hr & Ha). destruct (dab_ro_prog_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- exact (Hnp (recb_grec_in a Ha)).
- exact (Hnp (recb_spill_in a Ha)).
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HO (p, n) Hin) Ha Himg).
Qed.
(* arodata_okP along a journal of this call *)
Lemma dab_aro_at : forall STK0 sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK0 sp0 (dab_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK0 sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HO HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | exact (proj1 (dab_ro_prog_apart a Hro)) | exact Ho | exact He |].
apply fp_spares_closed; [exact (dab_FP_closed ly S W mem md O HAR HO) | exact (dab_ro_off_FP ly S W mem md O HAR HO a Hro)].
Qed.
(* a byte of the program's statics off a footprint is kept by a journal with that footprint *)
Lemma dab_PG_kept : forall STK0 sp0 FP0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k a,
ajournal SEGS B STK0 sp0 FP0 ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP0 -> Exists (in_zr a) recb_PG -> ~ inFP FP0 a -> rdW W' mem' a = rdW W mem a.
Proof.
intros STK0 sp0 FP0 ly S W mem md own ly' S' W' mem' md' k a HJ Hc HP Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (recb_ts_prog_m B HB); exact HP).
destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _).
apply F3; [exact (dab_prog_img a HP) | exact H1 | exact H2 | exact (fp_spares_closed _ _ Hc Hn)].
Qed.
(* a frame above a callee's window is kept by its journal when no footprint byte lies in the stack *)
Lemma dab_frame_call_kept : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k sp0 regs,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k ->
sp1 = sp0 - 32 -> alloc_ceiling <= sp0 - 32 -> sp0 <= 2 ^ 64 ->
(forall a, inFP FP1 a -> a < alloc_ceiling) ->
dab_frame_at (mrestrict (w_H Wc) memc) sp0 regs -> dab_frame_at (mrestrict (w_H W2) mem2) sp0 regs.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k sp0 regs HJ Hsp1 Hceil Hhi HFP Hfr j r Hj.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Hj3 : (j < length dab_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length dab_saved] in Hj3.
intros kk Hkk. rewrite <- (Hfr j r Hj kk Hkk). apply (mbyte_of_aview SEGS). apply F1.
- lia.
- lia.
- intros Hin. pose proof (HFP _ Hin). lia.
Qed.
(* the run of a segment whose regions are read-only keeps every byte *)
Lemma dab_run_same : forall E rs (H : word -> bool) (m m' : word -> option byte),
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hro HF a. apply (aview_eq_of SEGS). apply HF.
intros (r & Hin & Ha). pose proof (proj1 (Forall_forall _ _) Hro r Hin) as Hw. cbv beta in Hw. lia.
Qed.
(* the prologue's run writes only the frame *)
Lemma dab_run_frame : forall E (H : word -> bool) (m m' : word -> option byte) sp0,
bv_unsigned (ew E 2) = sp0 -> frame_of E [stack_region 32] (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' sp0 E2 HF a Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia.
intros (r & [<- | []] & Hr). cbn [stack_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E2 in Hr. lia.
Qed.
(* the last run writes only g_rec.state *)
Lemma dab_run_state : forall E (H : word -> bool) (m m' : word -> option byte),
bv_unsigned (ew E (A_HI 203)) = A_G_REC + OFF_STATE + 1548 ->
frame_of E [dab_frame; dab_stateH] (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' EH HF a Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia.
intros (r & [<- | [<- | []]] & Hr); cbn [dab_frame dab_stateH YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
[lia | rewrite EH in Hr; lia].
Qed.
(* one saved register in the frame the prologue wrote *)
Lemma dab_frame_field : forall (regs : bvmap 5 word) m sp0 cs od (n : nat) (rr : bv 5),
YP09.region_ok SEGS (Eimg (Ereg regs [])) m (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs) ->
spZ regs = sp0 -> In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs -> Z.of_nat n = bv_unsigned rr ->
val_mem SEGS m (sp0 + od) 8 (bv_unsigned (getr regs rr)).
Proof.
intros regs m sp0 cs od n rr HR Hsp Hin Hn.
assert (E2 : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = sp0) by (rewrite (ew_Eimg_Ereg_nat regs [] 2 2%bv eq_refl); exact Hsp).
pose proof (field_of_region_any _ m 2%nat sp0 cs (-32) 0 (-32) 0 od 8%N (SOff n 0) HR E2 Hin ltac:(cbn; lia)) as V.
cbn [sv_denot] in V. rewrite (ew_Eimg_Ereg_nat regs [] n rr Hn) in V. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in V.
pose proof (bv_unsigned_in_range 64 (getr regs rr)) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
rewrite Z.mod_small in V by (change (8 * Z.of_N 8) with 64; lia).
change (N.to_nat 8) with 8%nat in V. exact V.
Qed.
(* the caller's saved registers in the frame the prologue wrote (region 0 of the state at the call of record) *)
Lemma dab_frame_of_run : forall (regs : bvmap 5 word) m sp0,
YP09.region_ok SEGS (Eimg (Ereg regs [])) m
  (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
    [YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
spZ regs = sp0 -> dab_frame_at m sp0 regs.
Proof.
intros regs m sp0 HR Hsp j r Hj.
assert (Hj3 : (j < length dab_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length dab_saved] in Hj3.
assert (Hjj : (j = 0 \/ j = 1 \/ j = 2)%nat) by lia.
destruct Hjj as [-> | [-> | ->]]; cbn [nth_error dab_saved] in Hj; injection Hj as <-.
- replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 + -8) by lia.
  exact (dab_frame_field regs m sp0 _ (-8) 1 (Z_to_bv 5 1) HR Hsp ltac:(right; right; left; reflexivity) eq_refl).
- replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 + -16) by lia.
  exact (dab_frame_field regs m sp0 _ (-16) 8 (Z_to_bv 5 8) HR Hsp ltac:(right; left; reflexivity) eq_refl).
- replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 + -24) by lia.
  exact (dab_frame_field regs m sp0 _ (-24) 9 (Z_to_bv 5 9) HR Hsp ltac:(left; reflexivity) eq_refl).
Qed.
(* the bytes of the frame, kept under an equal view *)
Lemma dab_frame_same : forall (W W' : world SEGS) m m' sp0 regs,
(forall a, sp0 - 32 <= a < sp0 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
dab_frame_at (mrestrict (w_H W) m) sp0 regs -> dab_frame_at (mrestrict (w_H W') m') sp0 regs.
Proof.
intros W W' m m' sp0 regs HK Hfr j r Hj.
assert (Hj3 : (j < length dab_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length dab_saved] in Hj3.
intros kk Hkk. rewrite <- (Hfr j r Hj kk Hkk). apply (mbyte_of_aview SEGS). apply HK. lia.
Qed.
(* the registers a run keeps: every atom of dab_keep_list is still its own register *)
Lemma dab_keep_run : forall E ss ms regs0 extra, st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) dab_keep_list = true ->
dab_keep regs0 (ms_regs ms).
Proof.
intros E ss ms regs0 extra HS HA Hf r Hr.
exact (regs_kept_of_st_ok SEGS E ss ms regs0 extra dab_keep_list HS HA Hf r (dab_keep_in r Hr)).
Qed.
Lemma dab_keep_run_pi : forall E ss ms regs0 extra, st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) dab_keep_list = true ->
dab_keep regs0 (ms_regs ms).
Proof.
intros E ss ms regs0 extra HS HA Hf r Hr.
exact (regs_kept_of_st_ok_pi E ss ms regs0 extra dab_keep_list HS HA Hf r (dab_keep_in r Hr)).
Qed.
Lemma dab_agree : forall regs0 extra, env_agree 32 (Ereg regs0 extra) (Eimg (Ereg regs0 extra)).
Proof. intros regs0 extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* the entry's environment is the kit's CmdSnText.snt_E; its register reads in the form prreg leaves them *)
Lemma dab_sntE_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (snt_E regs) n = getr regs r.
Proof. intros regs n r Hn. unfold snt_E. exact (ew_Eimg_Ereg_nat regs [] n r Hn). Qed.
(* every byte of the footprint lies below the allocator's ceiling, so none is in the stack *)
Lemma dab_FP_low : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, inFP (dab_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a (r & Hr & Ha). pose proof dab_ceil as Hc.
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, REC_SIZE in Ha. lia.
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  pose proof (dab_blk ly S W mem md p n HAR (HO _ Hin)). lia.
Qed.
(* the representation, kept by a reader that agrees below the allocator's ceiling *)
Lemma dab_rep_low : forall ly S (W : world SEGS) mem md (rd rd' : reader) R O, AR SEGS B ly S W mem md ->
rec_repA B ly S rd R O -> (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) -> rec_repA B ly S rd' R O.
Proof.
intros ly S W mem md rd rd' R O HAR (Q & HA & HOQ) K. exists Q. split; [|exact HOQ]. pose proof dab_ceil as Hc.
apply (dab_arep_kept (ablocks B ly S) (ablocks B ly S) rd rd' R Q HA).
- intros a Ha. apply K. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
- intros [p n] i Hin Hi. cbn [fst snd] in *.
  pose proof (dab_blk ly S W mem md p n HAR (lay_blocks_in _ _ _ _ _ _ HA _ Hin)). apply K. lia.
- exact (lay_blocks_in _ _ _ _ _ _ HA).
Qed.
(* the representation across a callee with an empty footprint that keeps the allocator's state *)
Lemma dab_rep_nofp : forall STK1 sp1 ly S (W : world SEGS) m md own (W' : world SEGS) m' md' k R O,
ajournal SEGS B STK1 sp1 [] ly S W m md own ly S W' m' md' k ->
rec_repA B ly S (rdW W m) R O -> rec_repA B ly S (rdW W' m') R O.
Proof.
intros STK1 sp1 ly S W m md own W' m' md' k R O HJ (Q & HA & HOQ). exists Q. split; [|exact HOQ].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hc : ~ YI16.sink_open_fp []) by (intros (r & [] & _)).
assert (Hn : forall a, ~ inFP [] a) by (intros a (r & [] & _)).
apply (dab_arep_kept (ablocks B ly S) (ablocks B ly S) (rdW W m) (rdW W' m') R Q HA).
- intros a Ha. apply (dab_PG_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hc); [| apply Hn].
  destruct Ha as [Ha | Ha]; [apply recb_grec_in | apply recb_spill_in]; exact Ha.
- intros [p n] i Hin Hi. cbn [fst snd] in *.
  pose proof HA as HA'. pose proof (lay_blocks_in _ _ _ _ _ _ HA' _ Hin) as Hb.
  pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
  exact (F2 p n i Hb Hb ltac:(lia) (Hn _)).
- exact (lay_blocks_in _ _ _ _ _ _ HA).
Qed.

(* --- the last segment, 0x8cc8c .. 0x8cca0: g_rec.state := the digest, the frame popped, ret ------------------ *)
Lemma dab_c3 : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md R x O
  ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word) mem3 md3 O3,
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47 ->
ajournal SEGS B STK (spZ regs) (dab_FP O) ly S W mem md [] ly3 S3 W3 mem3 md3 (EV_DESCRIPTORS_ADD R) ->
bv_unsigned (getr regs3 2) = spZ regs - 32 ->
getr regs3 8 = Z_to_bv 64 (A_G_REC + OFF_STATE + 1548) ->
dab_frame_at (mrestrict (w_H W3) mem3) (spZ regs) regs ->
dab_keep regs regs3 ->
getr regs3 10 = w64 (mixcall (r_state R) 22 [x]) -> 0 <= r_state R < 2 ^ 64 ->
rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R 22 [x]) O3 ->
(forall pn, In pn O3 -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly3 S3)) ->
(forall pn, In pn (ablocks B ly3 S3) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O3) ->
blocks_bytes S3 <= blocks_bytes S + LIVE_DESCRIPTORS_ADD (Some x) ->
mo_le MT S S3 (XM_DESCRIPTORS_ADD MT R (Some x)) ->
SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + DAB_AFTER_MIX)) mem3 (seg_rom SEGS)) md3)
  (apost_base SEGS B STK (dab_FP O) regs ly S W mem md (EV_DESCRIPTORS_ADD R) (dab_Q ly S R (Some x) O)).
Proof.
intros ly S W regs mem md R x O ly3 S3 W3 regs3 mem3 md3 O3 Hra Hsp16 Hsp HJ Hsp3 H8 Hfr HK H10 Hh HREP HO1 HO2 HO3 HBB HML.
pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HAR3.
pose proof (mixcall_range (r_state R) 22 [x] Hh) as Hdig.
assert (Hwr : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W3) mem3) (A_G_REC + OFF_STATE + o)).
{ intros o Ho. apply dab_prog_writable. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
  cbn [fst snd]. unfold A_G_REC, OFF_STATE. lia. }
pose proof (dab_seat_mix cmd_val_his_PB W3 mem3 regs3 regs (spZ regs) 0 Hsp3 Hsp16 Hsp Hfr H8 Hwr) as HS.
assert (HEI : img_env VAL A_LIM (dab_E regs3 regs 0)) by (unfold dab_E; apply Eimg_env).
assert (UHI : bv_unsigned (ew (dab_E regs3 regs 0) (A_HI 203)) = A_G_REC + OFF_STATE + 1548).
{ unfold dab_E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite (dab_val_state_hi cmd_val_his_PB). apply unsigned_lit_small. unfold A_G_REC, OFF_STATE; lia. }
paj_run_shc RUNP RUNC HS HJ.
{ unfold dab_ssM. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact UHI | | apply awr_ok_nil].
  intros a Ha. cbn [dab_stateH YP09.r_wlo YP09.r_whi] in Ha.
  apply dab_awr_PG; [apply recb_grec_in | ]; unfold A_G_REC, OFF_STATE, REC_SIZE, A_G_QUITTING in *; lia. }
(* the state at the ret: g_rec.state holds the digest, every other byte is kept *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  rdW W3 (ms_mem ms) a = rdW W3 mem3 a) by (exact (dab_run_state _ (w_H W3) mem3 (ms_mem ms) UHI HFr)).
assert (UHI' : bv_unsigned (ew (dab_E regs3 regs 0) 603) = A_G_REC + OFF_STATE + 1548) by exact UHI.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  let r := eval vm_compute in (nth 1%nat (ss_mem ssx) dab_frame) in
  pose proof (st_ok_pi_region_nth _ ssx _ 1%nat r HS ltac:(vm_compute; reflexivity)) as HRst end.
cbn [ms_mem restrict] in HRst.
pose proof (field_of_region_any _ _ 603%nat (A_G_REC + OFF_STATE + 1548) _ _ _ _ _ (-1548) 8%N (SOff 10 0) HRst UHI'
  ltac:(left; reflexivity) ltac:(cbn; lia)) as V.
cbn [sv_denot] in V. rewrite (dab_E_reg regs3 regs 0 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H10 in V.
unfold w64 in V. rewrite unsigned_lit_small in V by lia. rewrite Z.mod_small in V by (change (8 * Z.of_N 8) with 64; lia).
replace (A_G_REC + OFF_STATE + 1548 + -1548) with (A_G_REC + OFF_STATE) in V by lia.
change (N.to_nat 8) with 8%nat in V.
pose proof (aval_mem_view SEGS (w_H W3) (ms_mem ms) _ 8 _ V) as Vst.
assert (HREPf : rec_repA B ly3 S3 (rdW W3 (ms_mem ms)) (descriptors_add_m R (Some x)) O3).
{ rewrite dab_model. cbn [sarg].
  apply (dab_rep_state B ly3 S3 ly3 S3 (rdW W3 mem3) (rdW W3 (ms_mem ms)) (rec_record R 22 [x]) O3 _ HREP Vst Hdig).
  - intros a Ha Hn. apply KM; [| exact Hn]. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia.
  - intros [p n] i Hin Hi. cbn [fst snd] in *.
    pose proof (dab_blk ly3 S3 W3 mem3 md3 p n HAR3 (dab_rep_blocks _ _ _ _ _ _ HREP _ Hin)) as (H1 & H2 & H3 & H4 & H5 & H6).
    apply KM; [lia |]. unfold A_G_REC, OFF_STATE in *. lia.
  - exact (dab_rep_blocks _ _ _ _ _ _ HREP). }
(* the registers the ret hands back *)
pose proof (dab_keep_run_pi _ _ _ regs3 (dab_extra regs 0) HS (dab_agree regs3 (dab_extra regs 0))
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9.
change 32%nat with (32 + 0)%nat in F1. rewrite dab_E_extra in F1 by lia.
change 33%nat with (32 + 1)%nat in F8. rewrite dab_E_extra in F8 by lia.
change 34%nat with (32 + 2)%nat in F9. rewrite dab_E_extra in F9 by lia.
cbn [dab_extra dab_saved map app nth] in F1, F8, F9.
rewrite (dab_E_reg regs3 regs 0 2 2%bv eq_refl), Hsp3 in F2.
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
split.
{ rewrite F1. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct (Z.eq_dec r 2) as [-> | N2].
  { replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F2.
    replace (spZ regs - 32 + 32) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
  destruct (Z.eq_dec r 8) as [-> | N8].
  { replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F8.
    replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
  destruct (Z.eq_dec r 9) as [-> | N9].
  { replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F9.
    replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
  assert (Hkr : dab_keep_r (Z_to_bv 5 r)).
  { unfold dab_keep_r. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. lia. }
  rewrite (KR _ Hkr). exact (HK _ Hkr). }
unfold dab_Q. exists O3. split; [exact HREPf|]. split; [exact HO1|]. split; [exact HO2|]. split; [exact HO3|].
split; [exact HBB | exact HML].
Qed.

(* --- the third segment, 0x8cc7c .. 0x8cc88: a0 := g_rec.state, a1 := the slot, the call of mix_call --------- *)
Lemma dab_c2 : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md R x O
  ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 O2,
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47 -> alloc_ceiling <= spZ regs - STK ->
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
st_nev S + EV_DESCRIPTORS_ADD R <= EV_MAX ->
ajournal SEGS B STK (spZ regs) (dab_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (EV_RECORD R + EV_ARG_S) ->
bv_unsigned (getr regs2 2) = spZ regs - 32 ->
getr regs2 9 = w64 (rec_slot R) ->
dab_frame_at (mrestrict (w_H W2) mem2) (spZ regs) regs ->
dab_keep regs regs2 ->
rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R 22 [x]) O2 ->
(forall pn, In pn O2 -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)) ->
(forall pn, In pn (ablocks B ly2 S2) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O2) ->
blocks_bytes S2 <= blocks_bytes S + LIVE_DESCRIPTORS_ADD (Some x) ->
mo_le MT S S2 (XM_DESCRIPTORS_ADD MT R (Some x)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + DAB_AFTER_ARG_S)) mem2 (seg_rom SEGS)) md2)
  (apost_base SEGS B STK (dab_FP O) regs ly S W mem md (EV_DESCRIPTORS_ADD R) (dab_Q ly S R (Some x) O)).
Proof.
intros ly S W regs mem md R x O ly2 S2 W2 regs2 mem2 md2 O2 Hra Hgp Htp Hsp16 Hsp Hcl HAR HO HROD HEV HJ
  Hsp2 H9 Hfr HK HREP HO1 HO2 HO3 HBB HML.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
pose proof HREP as (Q & HA & HOQ).
pose proof HA as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & Vst & _ & _ & _ & _ & Rst & _) & _).
rewrite dab_rec_record_state in Vst, Rst.
pose proof (dab_seat_arg_s VOBJS W2 mem2 regs2 regs (spZ regs) (r_state R) Hsp2 Hsp16 Hsp Hfr Vst Rst) as HS.
assert (HEI : img_env VAL A_LIM (dab_E regs2 regs (r_state R))) by (unfold dab_E; apply Eimg_env).
paj_run_shc RUNP RUNC HS HJ.
{ unfold dab_ssA. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (dab_keep_run _ _ _ regs2 (dab_extra regs (r_state R)) HS (dab_agree regs2 (dab_extra regs (r_state R)))
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (KMall : forall a, rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
{ apply (dab_run_same (dab_E regs2 regs (r_state R)) (ss_mem dab_ssA) (w_H W2) mem2 (ms_mem ms)); [|exact HFr].
  unfold dab_ssA. cbn [ss_mem]. repeat constructor; cbn; lia. }
rewrite (dab_E_reg regs2 regs (r_state R) 2 2%bv eq_refl) in P2.
assert (Psp : spZ (ms_regs ms) = spZ regs + -32) by (unfold spZ at 1; rewrite P2, Hsp2; lia).
change 35%nat with (32 + 3)%nat in P10. rewrite dab_E_extra in P10 by lia. cbn [dab_extra dab_saved map app nth] in P10.
rewrite (dab_E_reg regs2 regs (r_state R) 9 9%bv eq_refl), H9 in P11.
assert (P8' : getr (ms_regs ms) 8 = Z_to_bv 64 (A_G_REC + OFF_STATE + 1548)).
{ rewrite P8. unfold dab_E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
  change 603%nat with (A_HI 203). rewrite (dab_val_state_hi cmd_val_his_PB). reflexivity. }
destruct (dab_acall_slot _ _ R 22 [x] Q HA) as (P & HCALL0).
assert (HCALL : acall_at (ablocks B ly2 S2) (rdW W2 (ms_mem ms)) (rec_slot R) (22, [x]) P).
{ apply (dab_acall_at_kept _ _ (rdW W2 mem2) _ _ _ _ HCALL0);
  [intros pn Hpn; exact (acall_at_in _ _ _ _ _ HCALL0 pn Hpn) | intros i _; apply KMall | intros pn i _ _; apply KMall]. }
assert (HARO : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms))) by (exact (dab_aro_at _ _ O ly S W mem md _ _ _ _ _ _ _ HAR HO HJ HROD)).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
assert (HEVm : st_nev S2 + EV_MIX_CALL <= EV_MAX) by (unfold EV_DESCRIPTORS_ADD, EV_MIX_CALL in *; lia).
eapply SRr_bind;
[ eapply (cl_callS_na B LAWS W2 (ms_regs ms) (ms_mem ms) _ STK (spZ regs) (dab_FP O) ly S W mem md [] ly2 S2 _ _
    MIX_CALL_STK [] EV_MIX_CALL (-32) (getr (ms_regs ms) 1)
    (fun ly3 S3 W3 regs3 mem3 md3 => getr regs3 10 = w64 (mixcall (r_state R) 22 [x]) /\
      Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2) HJ Psp);
  [ reflexivity | lia | unfold MIX_CALL_STK, ESTACK; lia | rewrite dab_STK; unfold MIX_CALL_STK, ESTACK; lia
  | rewrite (KR 3%bv ltac:(left; reflexivity)), (HK 3%bv ltac:(left; reflexivity)); exact Hgp
  | rewrite (KR 4%bv ltac:(right; left; reflexivity)), (HK 4%bv ltac:(right; left; reflexivity)); exact Htp
  | reflexivity | rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | intros HPRE1; rewrite (dab_sig_mix_call cmd_sig_prog_PB); eapply SRr_mono;
    [ exact (TMIX_CALL fx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ (r_state R) (rec_slot R) (22, [x]) P HPRE1 HARO P10 Rst P11
        (dab_slot_mix R) HCALL (dab_ro_ok_of_aro ly2 S2 W2 (ms_mem ms) _ (proj1 HJ) HARO) HEVm)
    | intros W3 c3 _ H3; exact H3 ]
  | intros a (r & Hr & _); destruct Hr ]
| ].
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & Ha03 & _ & -> & ->).
rewrite P1. replace (BASE + 26460) with (BASE + DAB_AFTER_MIX) by reflexivity.
apply (dab_c3 ly S W regs mem md R x O ly2 S2 W3 regs3 mem3 md3 O2 Hra Hsp16 Hsp).
- replace (EV_DESCRIPTORS_ADD R) with (EV_RECORD R + EV_ARG_S + EV_MIX_CALL) by (unfold EV_DESCRIPTORS_ADD, EV_MIX_CALL; lia).
  exact HJ3.
- rewrite (dab_pres_bv _ _ 2%bv HP3 ltac:(unfold acallee_saved; left; reflexivity)). unfold spZ at 1 in Psp. rewrite Psp. lia.
- rewrite (dab_pres_bv _ _ 8%bv HP3 ltac:(unfold acallee_saved; right; right; right; left; reflexivity)). exact P8'.
- assert (Hsp1' : spZ regs + -32 = spZ regs - 32) by lia.
  assert (Hcl' : alloc_ceiling <= spZ regs - 32) by (pose proof dab_STK; lia).
  assert (Hhi : spZ regs <= 2 ^ 64) by lia.
  assert (Hfp : forall a, inFP [] a -> a < alloc_ceiling) by (intros a (r & [] & _)).
  exact (dab_frame_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs) regs HJc3 Hsp1' Hcl' Hhi Hfp
    (dab_frame_same W2 W2 mem2 (ms_mem ms) (spZ regs) regs (fun a _ => KMall a) Hfr)).
- exact (dab_keep_trans _ _ _ (dab_keep_trans _ _ _ HK KR) (dab_keep_pres _ _ HP3)).
- exact Ha03.
- exact Rst.
- apply (dab_rep_nofp _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3). exact (dab_rep_same _ _ _ _ _ _ _ HREP KMall).
- exact HO1.
- exact HO2.
- exact HO3.
- exact HBB.
- exact HML.
Qed.

(* --- the second segment, 0x8cc70 .. 0x8cc78: s1 := the slot, a1 := uri, the call of arg_s -------------------- *)
Lemma dab_c1 : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch R x O pu
  ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 F O1 q0 k0,
afn_pre SEGS B STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
st_nev S + EV_DESCRIPTORS_ADD R <= EV_MAX -> blocks_bytes S + LIVE_DESCRIPTORS_ADD (Some x) <= LIVE_MAX ->
mo_ok MT S (XM_DESCRIPTORS_ADD MT R (Some x)) ->
ajournal SEGS B STK (spZ regs) (dab_FP O) ly S W mem md [] ly1 S1 W1 mem1 md1 (EV_RECORD R) ->
bv_unsigned (getr regs1 2) = spZ regs - 32 ->
getr regs1 8 = w64 pu ->
getr regs1 10 = w64 (rec_slot R) ->
dab_frame_at (mrestrict (w_H W1) mem1) (spZ regs) regs ->
dab_keep regs regs1 ->
List.NoDup (ablocks B ly S) ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) ->
(forall pn, In pn F -> In pn O) ->
rec_repA B ly1 S1 (rdW W1 mem1) (rec_record R 22 []) O1 ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
blocks_bytes S1 <= blocks_bytes S ->
mo_le MT S S1 (XM_RECORD MT R) ->
(length (r_calls R) <= 16)%nat ->
In (q0, k0) (ablocks B ly1 S1) -> q0 <= pu -> pu + Z.of_nat (length x) + 1 <= q0 + k0 ->
astr_atR (rdW W1 mem1) pu x -> Z.of_nat (length x) + 1 <= LMAX + 1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + DAB_AFTER_RECORD)) mem1 (seg_rom SEGS)) md1)
  (apost_base SEGS B STK (dab_FP O) regs ly S W mem md (EV_DESCRIPTORS_ADD R) (dab_Q ly S R (Some x) O)).
Proof.
intros ly S W regs mem md ch R x O pu ly1 S1 W1 regs1 mem1 md1 F O1 q0 k0 HPRE HROD HO HEV HLIVE HMOK HJ
  Hsp1 H8 H10 Hfr HK HND HPerm HFO HREP HO1 HBB1 HML1 Hlen16 Hin0 Hq1 Hq2 HSTR HNL.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof dab_STK as HTS.
pose proof (proj1 HJ) as HAR1.
pose proof (dab_blk ly1 S1 W1 mem1 md1 q0 k0 HAR1 Hin0) as (Hq4096 & Hqc & Hk0 & Hr1 & Hr2 & Hoff).
assert (Hsp : 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47) by (rewrite HTS in Hslo; lia).
pose proof (dab_seat_record W1 mem1 regs1 regs (spZ regs) 0 Hsp1 Hsp16 Hsp Hfr) as HS.
assert (HEI : img_env VAL A_LIM (dab_E regs1 regs 0)) by (unfold dab_E; apply Eimg_env).
paj_run_shc RUNP RUNC HS HJ.
{ unfold dab_ssR. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (dab_keep_run _ _ _ regs1 (dab_extra regs 0) HS (dab_agree regs1 (dab_extra regs 0))
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (KMall : forall a, rdW W1 (ms_mem ms) a = rdW W1 mem1 a).
{ apply (dab_run_same (dab_E regs1 regs 0) (ss_mem dab_ssR) (w_H W1) mem1 (ms_mem ms)); [|exact HFr].
  unfold dab_ssR. cbn [ss_mem]. repeat constructor; cbn; lia. }
rewrite (dab_E_reg regs1 regs 0 2 2%bv eq_refl) in P2.
rewrite (dab_E_reg regs1 regs 0 8 8%bv eq_refl), H8 in P8.
rewrite (dab_E_reg regs1 regs 0 10 10%bv eq_refl), H10 in P9, P10.
rewrite (dab_E_reg regs1 regs 0 8 8%bv eq_refl), H8 in P11.
assert (Psp : spZ (ms_regs ms) = spZ regs + -32) by (unfold spZ at 1; rewrite P2, Hsp1; lia).
assert (HJl : forall a, inFP (dab_FP O) a -> a < alloc_ceiling) by (exact (dab_FP_low ly S W mem md O HAR HO)).
assert (HARO : arodata_okP SEGS RLO RHI B (rdW W1 (ms_mem ms))) by (exact (dab_aro_at _ _ O ly S W mem md _ _ _ _ _ _ _ HAR HO HJ HROD)).
assert (HSTR' : astr_argA B ly1 S1 (rdW W1 (ms_mem ms)) (in_roP SEGS RLO RHI) [] pu (Some x)).
{ cbv zeta. unfold astr_argA. split; [lia|]. split.
  { apply (dab_rastr_kept (rdW W1 mem1)); [exact HSTR | intros i _; apply KMall]. }
  split; [exact HNL|]. left. split; [exists q0, k0; split; [exact Hin0 | lia] | constructor]. }
assert (HTAIL : forall x', Some x = Some x' -> atail_vis SEGS W1 (ms_mem ms) (pu + Z.of_nat (length x'))).
{ intros x' Hx'. injection Hx' as <-. apply (dab_heap_tail_vis ly1 S1 W1 (ms_mem ms) _ q0 k0 _ (proj1 HJ) Hin0). lia. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
assert (HEVa : st_nev S1 + EV_ARG_S <= EV_MAX) by (unfold EV_DESCRIPTORS_ADD in HEV; lia).
assert (HLIVEa : blocks_bytes S1 + LIVE_ARG_S (Some x) <= LIVE_MAX) by (unfold LIVE_DESCRIPTORS_ADD in HLIVE; lia).
assert (HXA : 0 <= XM_ARG_S MT (Some x))
  by (unfold XM_ARG_S, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HMOKa : mo_ok MT S1 (XM_ARG_S MT (Some x))).
{ apply (mok_station MT S S1 (XM_DESCRIPTORS_ADD MT R (Some x)) (XM_RECORD MT R) (XM_ARG_S MT (Some x)) MTL HMOK HML1 HXA).
  unfold XM_DESCRIPTORS_ADD. lia. }
assert (HREPc : rec_repA B ly1 S1 (rdW W1 (ms_mem ms)) (rec_record R 22 []) O1)
  by (exact (dab_rep_same _ _ _ _ _ _ _ HREP KMall)).
assert (HFP1 : forall a, inFP (if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
  then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
        (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
         rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
  else []) a ->
  Exists (in_zr a) recb_PG /\ ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) /\ A_G_REC <= a < A_REC_SPILL + SC_SIZE).
{ intros a (r & Hr & Ha). cbn in Hr. replace a with (rec_slot R + (a - rec_slot R)) by lia.
  apply dab_slot_PG. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold CALL_SIZE; lia. }
eapply SRr_bind;
[ eapply (cl_callS_wide B LAWS W1 (ms_regs ms) (ms_mem ms) _ STK (spZ regs) (dab_FP O) ly S W mem md [] ly1 S1 _ _
    ARG_S_STK
    (if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
     then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
           (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
            rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
     else [])
    EV_ARG_S (-32) (getr (ms_regs ms) 1) []
    (fun ly' S' W' regs' mem' md' =>
      blocks_bytes S' <= blocks_bytes S1 + LIVE_ARG_S (Some x) /\
      mo_le MT S1 S' (XM_ARG_S MT (Some x)) /\
      ((Z.of_nat (length (@nil (list byte))) = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B ly1 S1) /\
        rec_repA B ly' S' (rdW W' mem') (rec_record R 22 []) O1) \/
       (Z.of_nat (length (@nil (list byte))) < REC_ARGS_MAX /\ exists p,
         4096 <= p < 2 ^ 64 /\
         Permutation (ablocks B ly' S') ((p, Z.of_nat (length (sarg (Some x))) + 1) :: ablocks B ly1 S1) /\
         Forall (fun qk => iv_apart p (Z.of_nat (length (sarg (Some x))) + 1) (fst qk) (snd qk)) (ablocks B ly1 S1) /\
         rec_repA B ly' S' (rdW W' mem') (rec_record R 22 ([] ++ [sarg (Some x)]))
           ((p, Z.of_nat (length (sarg (Some x))) + 1) :: O1))))
    HJ Psp);
  [ reflexivity | lia | unfold ARG_S_STK, ESTACK, XMALLOC_STK, ASTACK; lia
  | rewrite HTS; unfold ARG_S_STK, ESTACK, XMALLOC_STK, ASTACK; lia
  | rewrite (KR 3%bv ltac:(left; reflexivity)), (HK 3%bv ltac:(left; reflexivity)); exact Hgp
  | rewrite (KR 4%bv ltac:(right; left; reflexivity)), (HK 4%bv ltac:(right; left; reflexivity)); exact Htp
  | reflexivity | rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | apply achain_low; unfold s0Z; rewrite P8; unfold w64; rewrite unsigned_lit_small by lia; lia
  | intros HPRE1; rewrite (dab_sig_arg_s cmd_sig_prog_PB); eapply SRr_mono;
    [ exact (TARG_S fx ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ [] (rec_slot R) pu 22 [] (Some x) R O1 HPRE1 HARO
        (dab_ro_ok_of_aro ly1 S1 W1 (ms_mem ms) _ (proj1 HJ) HARO) P10 P11 eq_refl HREPc (or_introl HSTR') HTAIL
        HEVa HLIVEa HMOKa)
    | intros W2 c2 _ H2; exact H2 ]
  | intros a Ha; destruct (HFP1 a Ha) as (H1 & H2 & _); apply dab_awr_PG; assumption
  | intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hst _; exfalso;
    destruct (HFP1 a Ha) as (_ & _ & H3); pose proof dab_ceil; unfold A_G_REC, A_REC_SPILL, SC_SIZE in H3; lia ]
| ].
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HBB2 & HML2 & HK2).
destruct HK2 as [(Hsix & _) | (_ & p & Hp & HPerm2 & HFresh & HREP2)];
[exfalso; cbn in Hsix; unfold REC_ARGS_MAX in Hsix; lia|].
cbn [app sarg] in HPerm2, HFresh, HREP2.
rewrite P1. replace (BASE + 26444) with (BASE + DAB_AFTER_ARG_S) by reflexivity.
apply (dab_c2 ly S W regs mem md R x O ly2 S2 W2 regs2 mem2 md2 ((p, Z.of_nat (length x) + 1) :: O1)
  Hra Hgp Htp Hsp16 Hsp ltac:(lia) HAR HO HROD HEV HJ2).
- rewrite (dab_pres_bv _ _ 2%bv HP2 ltac:(unfold acallee_saved; left; reflexivity)). unfold spZ at 1 in Psp. rewrite Psp. lia.
- rewrite (dab_pres_bv _ _ 9%bv HP2 ltac:(unfold acallee_saved; right; right; right; right; left; reflexivity)). exact P9.
- apply (dab_frame_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs) regs HJc2); [lia | lia | lia | |].
  + intros a Ha. destruct (HFP1 a Ha) as (_ & _ & H3). pose proof dab_ceil.
    unfold A_G_REC, A_REC_SPILL, SC_SIZE in H3. lia.
  + apply (dab_frame_same W1 W1 mem1 (ms_mem ms)); [intros a _; apply KMall | exact Hfr].
- exact (dab_keep_trans _ _ _ (dab_keep_trans _ _ _ HK KR) (dab_keep_pres _ _ HP2)).
- exact HREP2.
- intros pn [<- | Hin].
  + destruct (in_dec recb_pair_dec (p, Z.of_nat (length x) + 1) O) as [HinO | HnO]; [left; exact HinO | right; intros HinS].
    apply (Permutation_in _ HPerm) in HinS. apply in_app_or in HinS as [H1 | H1]; [| exact (HnO (HFO _ H1))].
    pose proof (proj1 (Forall_forall _ _) HFresh _ H1) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia.
  + left. exact (proj1 (proj1 (HO1 pn) Hin)).
- intros pn HinS HnO. apply (Permutation_in _ (Permutation_sym HPerm2)). right.
  apply (Permutation_in _ HPerm) in HinS. apply in_app_or in HinS as [H1 | H1]; [exact H1 | exfalso; exact (HnO (HFO _ H1))].
- intros pn Hin2. apply (Permutation_in _ HPerm2) in Hin2. destruct Hin2 as [<- | H1]; [right; left; reflexivity|].
  assert (HinS : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; left; exact H1).
  destruct (in_dec recb_pair_dec pn O) as [HinO | HnO]; [right; right; apply HO1; split; [exact HinO|] | left; split; assumption].
  intros HinF. exact (list_nodup_app_disj (ablocks B ly1 S1) F pn (Permutation_NoDup HPerm HND) H1 HinF).
- unfold LIVE_DESCRIPTORS_ADD. lia.
- unfold XM_DESCRIPTORS_ADD. exact (mo_le_trans MT MTL _ _ _ _ _ HML1 HML2).
Qed.

(* --- the walk ---------------------------------------------------------------------------------------------- *)
Theorem tdescriptors_add_holds : tdescriptors_add_spec B MT.
Proof.
unfold tdescriptors_add_spec.
intros ly S W regs mem md ch pu uri R O HPRE HROD HROK H10 Hpu HSTR HREP HEV HLIVE HMOK.
destruct HSTR as (x & -> & HBLK & HSTRx & HNL & HAPO).
change (SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_add) regs mem md)
  (apost_base SEGS B STK (dab_FP O) regs ly S W mem md (EV_DESCRIPTORS_ADD R) (dab_Q ly S R (Some x) O))).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof dab_STK as HTS.
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by (exact (dab_rep_blocks _ _ _ _ _ _ HREP)).
pose proof HREP as (Q & HA & HOQ). pose proof HA as (_ & _ & _ & (Hlen16 & _) & _).
destruct HBLK as (q0 & k0 & Hin0 & Hq1 & Hq2).
pose proof (dab_blk ly S W mem md q0 k0 HAR Hin0) as (Hq4096 & Hqc & Hk0 & Hr1 & Hr2 & Hoff).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q0 k0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
assert (HND : List.NoDup (ablocks B ly S)) by (exact (recb_ablocks_nodup_m B ly S W mem md HAR)).
assert (HnO0 : ~ In (q0, k0) O).
{ intros Hq. pose proof (proj1 (Forall_forall _ _) HAPO _ Hq) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia. }
assert (Hsp : 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47) by (rewrite HTS in Hslo; lia).
pose proof (dab_entry W mem regs Hsp16 Hsp ltac:(intros a Ha; apply Hpres; rewrite HTS; lia)) as HS.
change (Eimg (Ereg regs [])) with (snt_E regs) in HS.
pose proof (ajournal_init SEGS B STK (dab_FP O) ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (snt_E regs)) by (unfold snt_E; apply Eimg_env).
assert (E2 : bv_unsigned (ew (snt_E regs) 2) = spZ regs) by (rewrite (dab_sntE_reg regs 2 2%bv eq_refl); reflexivity).
unfold cfg_at, w64.
paj_run_shc RUNP RUNC HS HJ.
{ unfold dab_ss0. cbn [ss_mem].
  eapply awr_ok_cons_stack; [reflexivity | exact E2 | cbn [stack_region YP09.r_wlo]; rewrite HTS; lia
  | cbn [stack_region YP09.r_whi]; lia | apply awr_ok_nil]. }
pose proof (dab_keep_run _ _ _ regs [] HS (dab_agree regs []) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let r := eval vm_compute in (nth 0%nat (ss_mem ssx) dab_frame) in
  pose proof (st_ok_region_nth _ ssx _ 0%nat r HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
pose proof (dab_frame_of_run regs _ (spZ regs) HR0 eq_refl) as Hfr0.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
rewrite (dab_sntE_reg regs 2 2%bv eq_refl) in P2.
rewrite (dab_sntE_reg regs 10 10%bv eq_refl), H10 in P8.
assert (Psp : spZ (ms_regs ms) = spZ regs + -32)
  by (unfold spZ at 1; rewrite P2; fold (spZ regs); rewrite unsigned_lit_small by lia; reflexivity).
(* what the prologue kept: everything below the frame *)
assert (KM0 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply (dab_run_frame (snt_E regs) (w_H W) mem (ms_mem ms) (spZ regs) E2 HFr); lia. }
assert (HREP0 : rec_repA B ly S (rdW W (ms_mem ms)) R O) by (exact (dab_rep_low ly S W mem md _ _ R O HAR HREP KM0)).
assert (HSTR0 : astr_atR (rdW W (ms_mem ms)) pu x).
{ apply (dab_rastr_kept (rdW W mem)); [exact HSTRx|]. intros i Hi. apply KM0. lia. }
assert (HJl : forall a, inFP (dab_FP O) a -> a < alloc_ceiling) by (exact (dab_FP_low ly S W mem md O HAR HO)).
assert (HARO0 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))) by (exact (dab_aro_at _ _ O ly S W mem md _ _ _ _ _ _ _ HAR HO HJ HROD)).
assert (HXA : 0 <= XM_ARG_S MT (Some x))
  by (unfold XM_ARG_S, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HEVr : st_nev S + EV_RECORD R <= EV_MAX) by (unfold EV_DESCRIPTORS_ADD, EV_ARG_S, EV_XMALLOC in HEV; lia).
assert (HMOKr : mo_ok MT S (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S (XM_RECORD MT R) (XM_DESCRIPTORS_ADD MT R (Some x)) HMOK). unfold XM_DESCRIPTORS_ADD. lia. }
(* the footprint of record: g_rec.ncalls, the slot's fn and nargs, and in the spill arm the recorder's blocks *)
assert (HFP1 : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a ->
  (Exists (in_zr a) recb_PG /\ ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) /\ A_G_REC <= a < A_REC_SPILL + SC_SIZE) \/
  (exists p n, In (p, n) O /\ p <= a < p + req_size n)).
{ intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
  - left. split; [apply recb_grec_in|]; unfold A_G_REC, OFF_NCALLS, REC_SIZE, A_G_QUITTING, A_REC_SPILL, SC_SIZE in *; lia.
  - left. replace a with (rec_slot R + (a - rec_slot R)) by lia. apply dab_slot_PG. unfold CALL_SIZE. lia.
  - right. revert Hr. destruct (Nat.ltb (length (r_calls R)) 16); [intros []|]. intros Hr.
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & HinO). cbn [fst snd] in Ha.
    exists p, n. split; [exact HinO | exact Ha]. }
assert (HFP1l : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> a < alloc_ceiling).
{ intros a Ha. destruct (HFP1 a Ha) as [(_ & _ & H3) | (p & n & HinO & Hpn)].
  - pose proof dab_ceil. unfold A_G_REC, A_REC_SPILL, SC_SIZE in H3. lia.
  - pose proof (dab_blk ly S W mem md p n HAR (HO _ HinO)). lia. }
eapply SRr_bind;
[ eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ STK (spZ regs) (dab_FP O) ly S W mem md [] ly S _ _
    RECORD_STK
    ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
     (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O))
    (EV_RECORD R) (-32) (getr (ms_regs ms) 1) []
    (fun ly' S' W' regs' mem' md' => exists (F O' : list (Z * Z)),
      getr regs' 10 = w64 (rec_slot R) /\
      Permutation (ablocks B ly S) (ablocks B ly' S' ++ F) /\
      Z.of_nat (length F) = rec_spill_frees R /\
      (forall pn, In pn F -> In pn O) /\
      rec_repA B ly' S' (rdW W' mem') (rec_record R 22 []) O' /\
      (forall pn, In pn O' <-> In pn O /\ ~ In pn F) /\
      blocks_bytes S' <= blocks_bytes S /\
      mo_le MT S S' (XM_RECORD MT R)) HJ Psp);
  [ reflexivity | lia | unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK; lia
  | rewrite HTS; unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK; lia
  | rewrite (KR 3%bv ltac:(left; reflexivity)); exact Hgp
  | rewrite (KR 4%bv ltac:(right; left; reflexivity)); exact Htp
  | reflexivity | rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | apply achain_low; unfold s0Z; rewrite P8; unfold w64; rewrite unsigned_lit_small by lia; lia
  | intros HPRE1; rewrite (dab_sig_record cmd_sig_prog_PB); eapply SRr_mono;
    [ exact (TRECORD fx ly S W (ms_regs ms) (ms_mem ms) _ [] 22 R O HPRE1 HARO0 P10
        ltac:(unfold REC_FN_COUNT; lia) HREP0 HEVr HMOKr)
    | intros W1 c1 _ H1; exact H1 ]
  | intros a Ha; destruct (HFP1 a Ha) as [(H1 & H2 & _) | (p & n & HinO & Hpn)];
    [apply dab_awr_PG; assumption | exact (dab_awr_blk _ _ O _ _ _ _ _ p n a HinO (HO _ HinO) Hpn)]
  | intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hst _; exfalso; pose proof (HFP1l a Ha); lia ]
| ].
cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HJc1 & HP1 &
  F & O1 & Ha01 & HPerm & _ & HFO & HREP1 & HO1 & HBB1 & HML1).
rewrite P1. replace (BASE + 26432) with (BASE + DAB_AFTER_RECORD) by reflexivity.
(* the string's block is none of the recorder's, so record keeps it live and keeps its bytes *)
assert (HinS1 : In (q0, k0) (ablocks B ly1 S1)).
{ pose proof (Permutation_in _ HPerm Hin0) as H. apply in_app_or in H as [H | H]; [exact H | exfalso; exact (HnO0 (HFO _ H))]. }
assert (HSTR1 : astr_atR (rdW W1 mem1) pu x).
{ apply (dab_rastr_kept (rdW W (ms_mem ms))); [exact HSTR0|]. intros i Hi.
  pose proof HJc1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  replace (pu + i) with (q0 + (pu - q0 + i)) by lia.
  apply (F2 q0 k0 (pu - q0 + i) Hin0 HinS1); [lia |].
  intros Hf. destruct (HFP1 _ Hf) as [(_ & _ & H3) | (p & n & HinO & Hpn)].
  - unfold A_G_REC, A_REC_SPILL, SC_SIZE in H3. lia.
  - assert (Hne : (q0, k0) <> (p, n)) by (intros Eq; rewrite Eq in HnO0; exact (HnO0 HinO)).
    pose proof (dab_pw_in _ _ (q0, k0) (p, n) Hpw Hin0 (HO _ HinO) Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    lia. }
assert (Hfr1 : dab_frame_at (mrestrict (w_H W1) mem1) (spZ regs) regs).
{ apply (dab_frame_call_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs) regs HJc1); [lia | lia | lia | exact HFP1l | exact Hfr0]. }
apply (dab_c1 ly S W regs mem md ch R x O pu ly1 S1 W1 regs1 mem1 md1 F O1 q0 k0 HPRE HROD HO HEV HLIVE HMOK).
- replace (EV_RECORD R) with (0 + EV_RECORD R) by lia. exact HJ1.
- rewrite (dab_pres_bv _ _ 2%bv HP1 ltac:(unfold acallee_saved; left; reflexivity)). unfold spZ at 1 in Psp. rewrite Psp. lia.
- rewrite (dab_pres_bv _ _ 8%bv HP1 ltac:(unfold acallee_saved; right; right; right; left; reflexivity)). exact P8.
- exact Ha01.
- exact Hfr1.
- exact (dab_keep_trans _ _ _ KR (dab_keep_pres _ _ HP1)).
- exact HND.
- exact HPerm.
- exact HFO.
- exact HREP1.
- exact HO1.
- exact HBB1.
- exact HML1.
- exact Hlen16.
- exact HinS1.
- exact Hq1.
- lia.
- exact HSTR1.
- exact HNL.
Qed.

End e.
End f.
End d.
