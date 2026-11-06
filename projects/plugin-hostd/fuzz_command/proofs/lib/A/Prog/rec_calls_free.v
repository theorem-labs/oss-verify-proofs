(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_free on the ASan build of plugin-hostd/fuzz_command
   (0x8953c, 96 instructions, two loops), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1..ACh3.v: one
   statement per loop point, each proved by a run of the symbolic executor from a fresh seed) and of this unit's
   sup_reply_code.v / xstrdup.v: the executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the free calls through afree04_sub (PaCall.v).
   Loop points: OUTER at 0x895b4 (entry i of the table, its nargs address in s2), INNER at 0x895e8 (argument a of
   entry i), TAIL at 0x89624 (the nargs store of entry i); the entry 0x8953c and the epilogue 0x89668 are walked once.
   Section hypotheses beyond the statement's AFREE4: HB (the image's symbol record, whose ts_prog names the program
   statics and whose zero-shadow ranges cover g_rec's call table and record.spill, CmdZsh.v cmd_addressable_in), TL
   (the free trampoline is the free rule's entry), MTL (the meter laws), PRW (prog_rw, YCbq.v: the program statics
   are writable) and IMG (the image facts, cmd_img_facts, whose cif_prog_img says every byte of
   g_rec / record.spill / g_quitting is in the image; CmdRecFacts.v).
   The nargs store into a table in a caller's side-stack frame is the frames-of-S clause of awr_byte (YCbq.v). The
   recorder conjuncts of the post are reduced to the reader lemmas of rec_calls_free_rep.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaDenot PaSB PaLibG PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdZsh rec_calls_free_c rec_calls_free_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module PRcf := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_free_c.

(* the symbolic states of the three loop points. Atoms: 32 the entry's base X = c + 56 i, 33 the shadow base, 34 the
   argument slot's address Y = X + 8 + 8 a, 35 the argument, 36 the nargs value, 37 the table c, 38 .. 50 the 13
   registers the prologue saves (ra, s0, s1, s2 .. s11) *)
Definition RCF_AF : Z := AF_rec_calls_free.
Definition rcf_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 33 0).
Definition rcf_Bx : sv := SOff 33 0.
Definition rcf_SH : list shent := [mkSHE 32 4 12; mkSHE 34 0 8].
Definition rcf_saved : list nat := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition rcf_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0
  (YP09.mkChunk 0 (CVal 8 (SOff 37 0)) :: map (fun j => YP09.mkChunk (104 - 8 * Z.of_nat j) (CVal 8 (SOff (38 + j) 0))) (seq 0 13)).
Definition rcf_na (w : bool) : YP09.region :=
  YP09.mkRegion (Some 32%nat) 4 8 4 (if w then 8 else 4) [YP09.mkChunk 4 (CVal 4 (SOff 36 0))].
Definition rcf_arg : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Definition rcf_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 4096 (2^47 - 2^23) 0);
  (33%nat, mkAF SB SB 0); (34%nat, mkAF 4096 (2^47 - 2^23) 0); (36%nat, mkAF 0 6 0)] [] [].
Definition rcf_regsO : list sv := Eval vm_compute in
  sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 4)) 21 (SOff 33 0)) 9 (SOff 32 8)) 23 (SOff 32 8).
Definition rcf_regsT : list sv := Eval vm_compute in sr_set rcf_regsO 24 (rcf_shx (SOff 32 4)).
Definition rcf_regsI : list sv := Eval vm_compute in
  sr_set (sr_set (sr_set rcf_regsT 26 (rcf_shx (SOff 34 0))) 22 (SOff 34 0)) 19 (SOff 34 0).
Definition rcf_ssO : sstate := mkSS (RCF_AF + 0x78) rcf_regsO [rcf_na false] None rcf_facts.
Definition rcf_ssI : sstate := mkSS (RCF_AF + 0xac) rcf_regsI [rcf_na false; rcf_arg] None rcf_facts.
Definition rcf_ssT : sstate := mkSS (RCF_AF + 0xe8) rcf_regsT [rcf_stk; rcf_na true] None rcf_facts.
(* the entry state: every register its own atom, atom 32 the shadow base, the frame and the GOT cells *)
Definition rcf_ssE : sstate := mkSS RCF_AF sr_atoms [stack_region 112; got_regionP; bcell_regionP 32] None
  (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0)] [] []).

Lemma rcf_saved_len : length rcf_saved = 13%nat. Proof. reflexivity. Qed.
Lemma le_byte_range : forall v n k, 0 <= YG0f.le_byte v n k < 256.
Proof. intros v n k. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma val_mem_of_aval : forall H (m : word -> option byte) a n v,
  aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. destruct (aview_byte SEGS H m (a + Z.of_nat k) _ (Hv k Hk)) as (b & Hb & Hbv & _).
rewrite Hb. f_equal. change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). rewrite Hbv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma aval_of_val_mem : forall H (m : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). apply Z.mod_small. apply le_byte_range.
Qed.
Lemma aval_mem_kept : forall (rd rd' : reader) a n v,
  (forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk Hv k Hkn. rewrite Hk by lia. apply Hv. exact Hkn. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's own hypothesis *)
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
(* the per-binary record: the record of the image's symbols (its ts_prog names the program statics),
   the free trampoline is the free rule's entry, the meter laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
(* the program-static facts: every byte of g_rec / record.spill / g_quitting is in the image
   (the image facts' cif_prog_img, CmdRecFacts.v), and the program statics are writable (prog_rw) *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a := cif_prog_img _ _ IMG.
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (c : Z) (ps : list (list (Z * Z))).
Hypothesis HPRE : afn_pre SEGS B REC_CALLS_FREE_STK ly S W regs mem md ch.
Hypothesis H10 : getr regs 10 = w64 c.
Hypothesis H11 : getr regs 11 = w64 (Z.of_nat (length ps)).
Hypothesis HN2 : (length ps <= 2)%nat.
Hypothesis HHOME : rcf_home B ly S W mem c (CALL_SIZE * Z.of_nat (length ps)).
Hypothesis HSLOT : forall i P, nth_error ps i = Some P ->
  (length P <= 6)%nat /\
  aval_mem (rdW W mem) (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
  forall a pn, nth_error P a = Some pn ->
    aval_mem (rdW W mem) (c + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
    In pn (ablocks B ly S).
Hypothesis HNODUP : NoDup (map fst (concat ps)).
Hypothesis HEV : st_nev S + EV_REC_CALLS_FREE ps <= EV_MAX.
Hypothesis HMOK : mo_ok MT S (XM_REC_CALLS_FREE MT ps).

#[local] Notation STK := REC_CALLS_FREE_STK.
#[local] Notation FP := (rcf_fp c ps).
#[local] Notation sp0 := (spZ regs).
#[local] Notation NE := (length ps).
Definition tbl_n : Z := CALL_SIZE * Z.of_nat (length ps).

(* the statement's post *)
Definition rcf_Q (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) /\
 (forall i, (i < length ps)%nat -> aval_mem (rdW W' mem') (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0) /\
 (forall j, 0 <= j < CALL_SIZE * Z.of_nat (length ps) -> ~ PRcf.nargs_field c (length ps) (c + j) ->
    rdW W' mem' (c + j) = rdW W mem (c + j)) /\
 (forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_G_REC + OFF_CALLS -> ps = l_calls Q ->
    rec_repA B ly' S' (rdW W' mem') (set_calls R (rcf_cleared (r_calls R)))
      (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_REC_SPILL -> ps = [l_spill Q] ->
    rec_repA B ly' S' (rdW W' mem') (set_spill R (fst (r_spill R), []))
      (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_G_REC REC_SIZE ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_REC_SPILL SC_SIZE ->
    (forall pn, In pn (concat ps) -> ~ In pn O) ->
    rec_repA B ly' S' (rdW W' mem') R O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_FREE /\
 mo_le MT S S' (XM_REC_CALLS_FREE MT ps).
Definition rcf_post : world SEGS -> config -> Prop :=
  apost_base SEGS B STK FP regs ly S W mem md (EV_REC_CALLS_FREE ps) rcf_Q.

(* the 13 registers the prologue saves and the table pointer, in the 112-byte frame *)
Definition rcf_frame (rd : reader) : Prop :=
 aval_mem rd (sp0 - 112) 8 c /\
 forall j r, nth_error rcf_saved j = Some r ->
   aval_mem rd (sp0 - 112 + (104 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))).
(* the arguments freed before argument a of entry i *)
Definition nP (i : nat) : nat := length (nth i ps []).
Definition rdone (i a : nat) : list (Z * Z) := concat (firstn i ps) ++ firstn a (nth i ps []).
Definition kd (i a : nat) : Z := Z.of_nat (length (rdone i a)).
Definition XE (i : nat) : Z := c + CALL_SIZE * Z.of_nat i.
Definition rcf_mid (i a : nat) lyc Sc (Wc : world SEGS) memc mdc : Prop :=
 ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc (kd i a) /\
 rcf_frame (rdW Wc memc) /\
 (forall j P, nth_error ps j = Some P ->
   aval_mem (rdW Wc memc) (c + CALL_SIZE * Z.of_nat j + CALL_OFF_NARGS) 4 (if (j <? i)%nat then 0 else Z.of_nat (length P))) /\
 Permutation (ablocks B ly S) (ablocks B lyc Sc ++ rdone i a) /\
 mo_le MT S Sc (kd i a * mo_free MT).
Definition rcf_rb (regs1 : bvmap 5 word) (i : nat) : Prop :=
 getr regs1 2 = Z_to_bv 64 (sp0 - 112) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
 getr regs1 8 = Z_to_bv 64 (Z.of_nat NE) /\ getr regs1 20 = Z_to_bv 64 (Z.of_nat i) /\ getr regs1 21 = Z_to_bv 64 SB /\
 getr regs1 9 = Z_to_bv 64 (XE i + 8) /\ getr regs1 23 = Z_to_bv 64 (XE i + 8) /\ getr regs1 18 = Z_to_bv 64 (XE i + 4).
Definition rcf_rt (regs1 : bvmap 5 word) (i : nat) : Prop :=
 rcf_rb regs1 i /\ getr regs1 24 = Z_to_bv 64 (SB + (XE i + 4) / 8).
Definition YA (i a : nat) : Z := XE i + 8 + 8 * Z.of_nat a.
Definition rcf_ri (regs1 : bvmap 5 word) (i a : nat) : Prop :=
 rcf_rt regs1 i /\ getr regs1 26 = Z_to_bv 64 (SB + YA i a / 8) /\ getr regs1 22 = Z_to_bv 64 (YA i a) /\
 getr regs1 19 = Z_to_bv 64 (YA i a) /\ getr regs1 25 = Z_to_bv 64 (Z.of_nat a).
Definition cfgA (off : Z) (regs1 : bvmap 5 word) memc mdc : config :=
 mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (RCF_AF + off))) memc (seg_rom SEGS)) mdc.
Definition ST_O (i : nat) : Prop := forall lyc Sc Wc memc mdc regs1,
 (i < NE)%nat -> rcf_mid i 0 lyc Sc Wc memc mdc -> rcf_rb regs1 i -> SRr SEGS Wc (cfgA 0x78 regs1 memc mdc) rcf_post.
Definition ST_I (i a : nat) : Prop := forall lyc Sc Wc memc mdc regs1,
 (i < NE)%nat -> (a < nP i)%nat -> rcf_mid i a lyc Sc Wc memc mdc -> rcf_ri regs1 i a ->
 SRr SEGS Wc (cfgA 0xac regs1 memc mdc) rcf_post.
Definition ST_T (i : nat) : Prop := forall lyc Sc Wc memc mdc regs1,
 (i < NE)%nat -> rcf_mid i (nP i) lyc Sc Wc memc mdc -> rcf_rt regs1 i -> SRr SEGS Wc (cfgA 0xe8 regs1 memc mdc) rcf_post.

(* ---------- the entry state's facts ---------- *)
Lemma rcf_pre : AR SEGS B ly S W mem md /\ astk_ok STK ly sp0 /\ (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem a).
Proof. destruct HPRE as (HAR & _ & _ & _ & _ & Hstk & Hpres & _). auto. Qed.
Lemma rcf_STK : STK = 16496. Proof. reflexivity. Qed.
Lemma rcf_sp0 : alloc_ceiling + 16496 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.
Proof.
destruct rcf_pre as (_ & (Hal & _ & Hceil & Hslo & Hshi & H47 & _) & _). rewrite rcf_STK in Hslo. lia.
Qed.
(* the table's home, in two cases: the program statics, or a frame of the entry's side stack *)
Definition home_frame : Prop :=
 exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
   frame_addr ly cid pos <= c /\ c + tbl_n <= frame_addr ly cid pos + fs_frame_bytes cid /\
   range_addressable (rdW W mem) SHADOW_OFF c tbl_n.
Definition home_prog : Prop := forall a, c <= a < c + tbl_n -> inFP cmd_PG a.
Lemma rcf_home_split : home_prog \/ home_frame.
Proof.
destruct HHOME as [[H1 H2] | [[H1 H2] | ((cid & pos & Hin & Hc & Hal & Hlo & Hhi) & _ & Hra)]].
- left. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|]. cbn [fst snd].
  unfold tbl_n, OFF_CALLS, REC_SIZE in *. lia.
- left. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity|]. cbn [fst snd].
  unfold tbl_n, SC_SIZE in *. lia.
- right. exists cid, pos. unfold tbl_n. auto 10.
Qed.
Lemma tbl_n_nonneg : 0 <= tbl_n. Proof. unfold tbl_n, CALL_SIZE. lia. Qed.
Lemma inFP_cmd_PG_range : forall a, inFP cmd_PG a -> 0x5e3740 <= a < 0x5e3c64.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma home_frame_bounds : home_frame ->
 exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= c /\ c + tbl_n <= frame_addr ly cid pos + fs_frame_bytes cid /\
   4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
   in_app (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros (cid & pos & Hin & _ & _ & Hlo & Hhi & _). exists cid, pos.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos (proj1 rcf_pre) Hin) as (H1 & H2 & H3). auto 10.
Qed.
(* every byte of a non-empty table lies in application memory below alloc_ceiling *)
Lemma tbl_bounds : forall a, c <= a < c + tbl_n ->
 4096 <= c /\ c + tbl_n <= alloc_ceiling /\ (a < kLowShadowBeg \/ kHighShadowEnd <= a).
Proof.
intros a Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct rcf_home_split as [HP | HF].
- pose proof (inFP_cmd_PG_range a (HP a Ha)) as R.
  pose proof (inFP_cmd_PG_range c (HP c ltac:(lia))) as Rc.
  pose proof (inFP_cmd_PG_range (c + tbl_n - 1) (HP (c + tbl_n - 1) ltac:(lia))) as Re.
  unfold kLowShadowBeg. lia.
- destruct (home_frame_bounds HF) as (cid & pos & _ & Hlo & Hhi & H4096 & Hceil & Happ).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. split; [lia|]. split; [lia|]. lia.
Qed.
(* the program statics of the record *)
Lemma pg_prog : forall a, inFP cmd_PG a ->
 Exists (in_zr a) (as_prog_static B) /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha.
assert (HP : Exists (in_zr a) (as_prog_static B)).
{ rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
  destruct Ha as (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha.
  - apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
destruct (prog_static_sep B a (ts_ok B HB) HP) as (H1 & H2 & _). auto.
Qed.
(* the footprint: the n nargs fields and the argument blocks *)
Lemma fp_cases : forall a, inFP FP a ->
 PRcf.nargs_field c NE a \/ exists p m, In (p, m) (concat ps) /\ p <= a < p + req_size m.
Proof.
intros a (r & Hr & Ha). unfold rcf_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. apply in_map_iff in Hr as (i & <- & Hi). apply in_seq in Hi. cbn [fst snd] in Ha.
  exists i. split; [lia|]. unfold CALL_SIZE, CALL_OFF_NARGS in Ha. lia.
- right. apply inFP_ablocks_fp_inv. exists r. split; [exact Hr | exact Ha].
Qed.
Lemma fp_nargs : forall i a, (i < NE)%nat -> c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS <= a < c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS + 4 ->
 inFP FP a.
Proof.
intros i a Hi Ha. exists (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS, c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS + 4).
split; [|cbn [fst snd]; lia]. unfold rcf_fp. apply in_or_app. left. apply in_map_iff. exists i.
split; [reflexivity | apply in_seq; lia].
Qed.
Lemma fp_block : forall p m j, In (p, m) (concat ps) -> 0 <= j < req_size m -> inFP FP (p + j).
Proof.
intros p m j Hin Hj. destruct (inFP_ablocks_fp (concat ps) p m j Hin Hj) as (r & Hr & Ha).
exists r. split; [unfold rcf_fp; apply in_or_app; right; exact Hr | exact Ha].
Qed.
(* every argument is a live block of the entry *)
Lemma arg_live : forall pn, In pn (concat ps) -> In pn (ablocks B ly S).
Proof.
intros pn Hin. apply in_concat in Hin as (P & HP & Hpn).
apply In_nth_error in HP as (i & Hi). apply In_nth_error in Hpn as (a & Ha).
exact (proj2 (proj2 (proj2 (HSLOT i P Hi)) a pn Ha)).
Qed.
Lemma arg_bounds : forall p m, In (p, m) (concat ps) ->
 4096 <= p /\ p + req_size m <= alloc_ceiling /\ in_app p (req_size m) /\ 0 <= m /\
 (forall j, p <= j < p + req_size m -> ~ in_img SEGS j).
Proof.
intros p m Hin. pose proof (arg_live _ Hin) as Hl.
destruct (al_blocks _ _ LAWS ly S W mem md p m (proj1 rcf_pre) Hl) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
split; [lia|]. split; [lia|]. split; [exact Happ|]. split; [lia|].
intros j Hj. exact (blk_img SEGS B LAWS ly S W mem md p m j (proj1 rcf_pre) Hl Hj).
Qed.
(* the table and the argument blocks are apart *)
Lemma tbl_arg_apart : forall p m j, In (p, m) (concat ps) -> p <= j < p + req_size m -> ~ (c <= j < c + tbl_n).
Proof.
intros p m j Hin Hj Ht. destruct rcf_home_split as [HP | HF].
- exact (proj2 (proj2 (proj2 (proj2 (arg_bounds p m Hin)))) j Hj (cif_prog_img j (HP j Ht))).
- destruct HF as (cid & pos & Hfin & _ & _ & Hlo & Hhi & _).
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md p m cid pos (proj1 rcf_pre) (arg_live _ Hin) Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma fp_tbl : forall a, c <= a < c + tbl_n -> inFP FP a -> PRcf.nargs_field c NE a.
Proof.
intros a Ha Hf. destruct (fp_cases a Hf) as [H | (p & m & Hin & Hr)]; [exact H|].
exfalso. exact (tbl_arg_apart p m a Hin Hr Ha).
Qed.
Lemma fp_app : forall x, inFP FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x.
Proof.
intros x Hx. destruct (fp_cases x Hx) as [(i & Hi & Hr) | (p & m & Hin & Hr)].
- assert (Ht : c <= x < c + tbl_n) by (unfold tbl_n, CALL_SIZE in *; nia).
  exact (proj2 (proj2 (tbl_bounds x Ht))).
- destruct (arg_bounds p m Hin) as (_ & _ & Happ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma fp_closed : ~ YI16.sink_open_fp FP.
Proof.
intros (r & Hr & Ha). assert (Hf : inFP FP 0) by (exists r; split; [exact Hr | exact Ha]).
destruct (fp_cases 0 Hf) as [(i & Hi & Hr0) | (p & m & Hin & Hr0)].
- assert (Ht : c <= c + CALL_SIZE * Z.of_nat i + 4 < c + tbl_n) by (unfold tbl_n, CALL_SIZE in *; nia).
  pose proof (proj1 (tbl_bounds _ Ht)). lia.
- pose proof (proj1 (arg_bounds p m Hin)). lia.
Qed.
(* the frame of an entry journal is the entry's frame *)
Lemma jr_frames : forall lyc Sc Wc memc mdc k, ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 frames Sc = frames S /\ (forall cid pos, frame_addr lyc cid pos = frame_addr ly cid pos).
Proof.
intros lyc Sc Wc memc mdc k HJ. pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc (proj1 rcf_pre) Hly) as (_ & Efa & _).
split; [exact Hfrs | exact Efa].
Qed.
(* (T1) a table byte outside the nargs fields keeps its entry value *)
Lemma tbl_keep : forall lyc Sc Wc memc mdc k a, ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 c <= a < c + tbl_n -> ~ PRcf.nargs_field c NE a -> rdW Wc memc a = rdW W mem a.
Proof.
intros lyc Sc Wc memc mdc k a HJ Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
assert (Hnf : ~ inFP FP a) by (intros Hf; exact (Hn (fp_tbl a Ha Hf))).
destruct rcf_home_split as [HP | HF].
- destruct (pg_prog a (HP a Ha)) as (_ & Ho & He).
  apply F3; [exact (cif_prog_img a (HP a Ha)) | exact Ho | exact He | exact (fp_spares_closed FP a fp_closed Hnf)].
- destruct HF as (cid & pos & Hfin & _ & _ & Hlo & Hhi & _).
  apply (F4 cid pos a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; unfold tbl_n in *; lia | exact Hnf].
Qed.
(* (T2) every part of the table is usable in the shadow, in every state of an entry journal *)
Lemma tbl_addr : forall lyc Sc Wc memc mdc k a len, ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 c <= a -> a + len <= c + tbl_n -> range_addressable (rdW Wc memc) SHADOW_OFF a len.
Proof.
intros lyc Sc Wc memc mdc k a len HJ Hlo Hhi.
destruct (Z_lt_le_dec 0 len) as [Hl | Hl]; [|apply range_addressable_nil; lia].
destruct HHOME as [[H1 H2] | [[H1 H2] | ((cid & pos & Hfin & Hcid & Hal & Hflo & Hfhi) & _ & Hra)]].
- apply (cmd_addressable_in SEGS B LAWS HB lyc Sc Wc memc mdc (0xada00, 0x5e3b00 - 0xada00) a len (proj1 HJ));
    [vm_compute; repeat first [left; reflexivity | right] | reflexivity | reflexivity | |];
    cbn [fst snd]; unfold tbl_n, A_G_REC, OFF_CALLS, REC_SIZE in *; lia.
- apply (cmd_addressable_in SEGS B LAWS HB lyc Sc Wc memc mdc (0x5e3be0, 0x5e3c18 - 0x5e3be0) a len (proj1 HJ));
    [vm_compute; repeat first [left; reflexivity | right] | reflexivity | reflexivity | |];
    cbn [fst snd]; unfold tbl_n, A_REC_SPILL, SC_SIZE in *; lia.
- unfold tbl_n in *.
  apply (range_addressable_entry_frame SEGS B LAWS STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k cid pos a len HJ Hfin Hcid);
    [lia | lia | exact Hal | exact fp_app | exact (proj1 rcf_pre) |].
  apply (range_addressable_sub _ _ c (CALL_SIZE * Z.of_nat (length ps))); [exact Hra | lia | lia].
Qed.
(* (T3) the table is writable *)
Lemma tbl_wr : forall lyc Sc Wc memc mdc k a, ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 c <= a < c + tbl_n -> writable_at SEGS (mrestrict (w_H Wc) memc) a.
Proof.
intros lyc Sc Wc memc mdc k a HJ Ha.
destruct rcf_home_split as [HP | HF].
- exact (PRW _ a (proj1 (pg_prog a (HP a Ha)))).
- destruct HF as (cid & pos & Hfin & _ & _ & Hlo & Hhi & _).
  destruct (jr_frames lyc Sc Wc memc mdc k HJ) as [Efr Efa].
  assert (Hfc : In (cid, pos) (frames Sc)) by (rewrite Efr; exact Hfin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ) Hfc) as (_ & _ & Hfb & _).
  apply (apresent_writable SEGS). apply (proj1 (Hfb a ltac:(rewrite Efa; unfold tbl_n in *; lia))).
Qed.
(* (T4) the nargs store is a footprint write the journal admits *)
Lemma tbl_awr : forall lyc Sc Wc memc mdc k a, ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 c <= a < c + tbl_n -> inFP FP a ->
 awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [] a.
Proof.
intros lyc Sc Wc memc mdc k a HJ Ha Hf. right; right; right; right.
destruct rcf_home_split as [HP | HF].
- left. split; [exact Hf|]. split; [exact (proj1 (pg_prog a (HP a Ha))) | exact (cif_prog_img a (HP a Ha))].
- right; right. split; [exact Hf|]. destruct HF as (cid & pos & Hfin & _ & _ & Hlo & Hhi & _).
  destruct (jr_frames lyc Sc Wc memc mdc k HJ) as [_ Efa].
  exists cid, pos. split; [exact Hfin|]. left. unfold in_zr. cbn [fst snd]. rewrite Efa. unfold tbl_n in *. lia.
Qed.
(* the entry's bounds for every table entry *)
Lemma xe_bounds : forall i, (i < NE)%nat ->
 4096 <= c /\ c <= XE i /\ XE i + 56 <= c + tbl_n /\ c + tbl_n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000.
Proof.
intros i Hi. pose proof asan_consts as (C1 & _).
assert (Ht : c <= c < c + tbl_n) by (unfold tbl_n, CALL_SIZE; lia).
destruct (tbl_bounds c Ht) as (H1 & H2 & _). unfold XE, tbl_n, CALL_SIZE in *. split; [lia|]. split; [lia|].
split; [nia | lia].
Qed.
Lemma nth_nP : forall i P, nth_error ps i = Some P -> nP i = length P.
Proof. intros i P H. unfold nP. rewrite (nth_error_nth ps i [] H). reflexivity. Qed.
Lemma nP_le6 : forall i, (i < NE)%nat -> (nP i <= 6)%nat.
Proof.
intros i Hi. destruct (nth_error ps i) as [P|] eqn:E; [|apply nth_error_None in E; lia].
rewrite (nth_nP i P E). exact (proj1 (HSLOT i P E)).
Qed.

(* ---------- the valuation of a loop point ---------- *)
Definition rcf_extra (Xv Yv Pv NAv : Z) : list word :=
 map (Z_to_bv 64) [Xv; SB; Yv; Pv; NAv; c] ++ map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) rcf_saved.
Definition rcf_E (regs1 : bvmap 5 word) (Xv Yv Pv NAv : Z) : env := Eimg (Ereg regs1 (rcf_extra Xv Yv Pv NAv)).
Lemma rcf_E_reg : forall regs1 Xv Yv Pv NAv n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 Xv Yv Pv NAv) n = getr regs1 r.
Proof. intros regs1 Xv Yv Pv NAv n r Hn. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma rcf_E_x : forall regs1 Xv Yv Pv NAv j, ew (rcf_E regs1 Xv Yv Pv NAv) (32 + j) = nth j (rcf_extra Xv Yv Pv NAv) (Z_to_bv 64 0) \/ (A_TEXT <= 32 + j)%nat.
Proof.
intros regs1 Xv Yv Pv NAv j. destruct (Nat.lt_ge_cases (32 + j) A_TEXT) as [H|H]; [left|right; exact H].
unfold rcf_E. rewrite Eimg_low by exact H. apply ew_Ereg_extra.
Qed.
Lemma rcf_E_atoms : forall regs1 Xv Yv Pv NAv,
 ew (rcf_E regs1 Xv Yv Pv NAv) 32 = Z_to_bv 64 Xv /\ ew (rcf_E regs1 Xv Yv Pv NAv) 33 = Z_to_bv 64 SB /\
 ew (rcf_E regs1 Xv Yv Pv NAv) 34 = Z_to_bv 64 Yv /\ ew (rcf_E regs1 Xv Yv Pv NAv) 35 = Z_to_bv 64 Pv /\
 ew (rcf_E regs1 Xv Yv Pv NAv) 36 = Z_to_bv 64 NAv /\ ew (rcf_E regs1 Xv Yv Pv NAv) 37 = Z_to_bv 64 c /\
 (forall j r, nth_error rcf_saved j = Some r -> ew (rcf_E regs1 Xv Yv Pv NAv) (38 + j) = getr regs (Z_to_bv 5 (Z.of_nat r))).
Proof.
intros regs1 Xv Yv Pv NAv.
assert (X : forall j, (j < 19)%nat -> ew (rcf_E regs1 Xv Yv Pv NAv) (32 + j) = nth j (rcf_extra Xv Yv Pv NAv) (Z_to_bv 64 0)).
{ intros j Hj. destruct (rcf_E_x regs1 Xv Yv Pv NAv j) as [H|H]; [exact H | unfold A_TEXT in H; lia]. }
split; [exact (X 0%nat ltac:(lia))|]. split; [exact (X 1%nat ltac:(lia))|]. split; [exact (X 2%nat ltac:(lia))|].
split; [exact (X 3%nat ltac:(lia))|]. split; [exact (X 4%nat ltac:(lia))|]. split; [exact (X 5%nat ltac:(lia))|].
intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- rcf_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
replace (38 + j)%nat with (32 + (6 + j))%nat by lia. rewrite (X (6 + j)%nat ltac:(lia)). unfold rcf_extra.
rewrite app_nth2 by (cbn; lia). cbn [length map]. replace (6 + j - 6)%nat with j by lia.
rewrite (nth_indep _ _ (getr regs (Z_to_bv 5 (Z.of_nat 0)))) by (rewrite length_map; rewrite rcf_saved_len; exact Hj13).
rewrite (map_nth (fun r => getr regs (Z_to_bv 5 (Z.of_nat r)))). rewrite (nth_error_nth rcf_saved j 0%nat Hj). reflexivity.
Qed.
Ltac rcf_reg_tac EE E32 E33 E34 :=
 lazymatch goal with |- _ = sv_denot ?E (sr_get ?sr ?rr) => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end;
 first
 [ rewrite getr_zero; reflexivity
 | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
 | cbn [sv_denot]; rewrite E32, unsigned_lit_small by lia; assumption
 | cbn [sv_denot]; rewrite E33, unsigned_lit_small by (unfold SB; lia); rewrite Z.add_0_r; assumption
 | cbn [sv_denot]; rewrite E34, unsigned_lit_small by lia; rewrite Z.add_0_r; assumption
 | rewrite (denot_shx _ 32 33 4 _ SB E32 E33) by (unfold SB; lia); assumption
 | rewrite (denot_shx _ 34 33 0 _ SB E34 E33) by (unfold SB; lia); rewrite Z.add_0_r; assumption ].
Lemma rcf_regs_okO : forall regs1 i Yv Pv NAv, (i < NE)%nat -> 0 <= Yv < 2 ^ 63 -> rcf_rb regs1 i ->
 regs_ok (rcf_E regs1 (XE i) Yv Pv NAv) rcf_regsO regs1.
Proof.
intros regs1 i Yv Pv NAv Hi HY (R2 & R3 & R4 & R8 & R20 & R21 & R9 & R23 & R18).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5).
destruct (rcf_E_atoms regs1 (XE i) Yv Pv NAv) as (E32 & E33 & E34 & _).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 (XE i) Yv Pv NAv) n = getr regs1 r)
  by (intros; apply rcf_E_reg; assumption).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr]; [rcf_reg_tac EE E32 E33 E34|]). destruct Hr.
Qed.
Lemma rcf_regs_okT : forall regs1 i Yv Pv NAv, (i < NE)%nat -> 0 <= Yv < 2 ^ 63 -> rcf_rt regs1 i ->
 regs_ok (rcf_E regs1 (XE i) Yv Pv NAv) rcf_regsT regs1.
Proof.
intros regs1 i Yv Pv NAv Hi HY ((R2 & R3 & R4 & R8 & R20 & R21 & R9 & R23 & R18) & R24).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5).
destruct (rcf_E_atoms regs1 (XE i) Yv Pv NAv) as (E32 & E33 & E34 & _).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 (XE i) Yv Pv NAv) n = getr regs1 r)
  by (intros; apply rcf_E_reg; assumption).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr]; [rcf_reg_tac EE E32 E33 E34|]). destruct Hr.
Qed.
Lemma rcf_regs_okI : forall regs1 i a Pv NAv, (i < NE)%nat -> (a < nP i)%nat -> rcf_ri regs1 i a ->
 regs_ok (rcf_E regs1 (XE i) (YA i a) Pv NAv) rcf_regsI regs1.
Proof.
intros regs1 i a Pv NAv Hi Ha (((R2 & R3 & R4 & R8 & R20 & R21 & R9 & R23 & R18) & R24) & R26 & R22 & R19 & R25).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof (nP_le6 i Hi) as H6.
assert (HY : 0 <= YA i a < 2 ^ 63) by (unfold YA, XE, CALL_SIZE in *; lia).
destruct (rcf_E_atoms regs1 (XE i) (YA i a) Pv NAv) as (E32 & E33 & E34 & _).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 (XE i) (YA i a) Pv NAv) n = getr regs1 r)
  by (intros; apply rcf_E_reg; assumption).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr]; [rcf_reg_tac EE E32 E33 E34|]). destruct Hr.
Qed.
(* ---------- the regions, facts and shadow entries of a loop point ---------- *)
Lemma rg_na : forall E (m : word -> option byte) Xv NAv (w : bool),
 bv_unsigned (ew E 32) = Xv -> ew E 36 = Z_to_bv 64 NAv -> 0 <= NAv < 2 ^ 32 -> 0 <= Xv -> Xv + 8 <= 2 ^ 64 ->
 val_mem SEGS m (Xv + 4) 4 NAv -> (w = true -> forall o, 4 <= o < 8 -> writable_at SEGS m (Xv + o)) ->
 region_ok SEGS E m (rcf_na w).
Proof.
intros E m Xv NAv w HX HNA Hr H0 H8 Hv Hw. unfold region_ok, rcf_na.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite HX.
split; [lia|]. split; [lia|]. split.
- intros o Ho. destruct w; [apply Hw; [reflexivity | lia] | lia].
- apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E m Xv 4 4%N (SOff 36 0) NAv); [| cbn; lia | cbn; lia | exact Hv].
  cbn [sv_denot]. rewrite HNA, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
Qed.
Lemma rg_arg : forall E (m : word -> option byte) Yv Pv,
 bv_unsigned (ew E 34) = Yv -> ew E 35 = Z_to_bv 64 Pv -> 0 <= Pv < 2 ^ 64 -> 0 <= Yv -> Yv + 8 <= 2 ^ 64 ->
 val_mem SEGS m Yv 8 Pv -> region_ok SEGS E m rcf_arg.
Proof.
intros E m Yv Pv HY HP Hr H0 H8 Hv. unfold region_ok, rcf_arg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite HY.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E m Yv 0 8%N (SOff 35 0) Pv); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hv].
cbn [sv_denot]. rewrite HP, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
Qed.
Lemma rg_stk : forall E (m : word -> option byte) sp1,
 bv_unsigned (ew E 2) = sp1 -> ew E 37 = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 ->
 (forall j r, nth_error rcf_saved j = Some r -> ew E (38 + j) = getr regs (Z_to_bv 5 (Z.of_nat r))) ->
 0 <= sp1 -> sp1 + 112 <= 2 ^ 64 ->
 val_mem SEGS m sp1 8 c ->
 (forall j r, nth_error rcf_saved j = Some r ->
   val_mem SEGS m (sp1 + (104 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))) ->
 region_ok SEGS E m rcf_stk.
Proof.
intros E m sp1 Hsp E37 Hc ES H0 H1 Vc VS. unfold region_ok.
cbn [rcf_stk YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hsp.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons.
- apply (chunk_ok_val SEGS E m sp1 0 8%N (SOff 37 0) c); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc].
  cbn [sv_denot]. rewrite E37, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
- apply Forall_forall. intros ch0 Hch. apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error rcf_saved j) as [r|] eqn:Er; [| apply nth_error_None in Er; rewrite rcf_saved_len in Er; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  apply (chunk_ok_val SEGS E m sp1 (104 - 8 * Z.of_nat j) 8%N (SOff (38 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))));
    [| cbn; lia | cbn; lia | exact (VS j r Er)].
  cbn [sv_denot]. rewrite (ES j r Er), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma rcf_facts_ok : forall E Xv Yv NAv,
 bv_unsigned (ew E 2) = sp0 - 112 -> ew E 32 = Z_to_bv 64 Xv -> ew E 33 = Z_to_bv 64 SB -> ew E 34 = Z_to_bv 64 Yv ->
 ew E 36 = Z_to_bv 64 NAv ->
 4096 <= Xv <= 2 ^ 47 - 2 ^ 23 -> 4096 <= Yv <= 2 ^ 47 - 2 ^ 23 -> 0 <= NAv <= 6 -> facts_ok E rcf_facts.
Proof.
intros E Xv Yv NAv H2 H32 H33 H34 H36 HX HY HN. split; [|split; exact I].
cbn [rcf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H2, H32, H33, H34, H36, !unsigned_lit_small by (unfold SB; lia).
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
repeat split; try lia.
Qed.
Lemma rcf_shok : forall lyc Sc Wc memc mdc k E Xv Yv,
 ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 ew E 32 = Z_to_bv 64 Xv -> ew E 33 = Z_to_bv 64 SB -> ew E 34 = Z_to_bv 64 Yv ->
 c <= Xv -> Xv + 12 <= c + tbl_n -> c <= Yv -> Yv + 8 <= c + tbl_n ->
 sh_ok SEGS rcf_Bx rcf_SH E (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Wc memc mdc k E Xv Yv HJ H32 H33 H34 HX1 HX2 HY1 HY2.
assert (Ht : c <= c < c + tbl_n) by lia. destruct (tbl_bounds c Ht) as (B1 & B2 & _). pose proof asan_consts as (C1 & _).
assert (UB : U E rcf_Bx = SHADOW_OFF) by (unfold rcf_Bx; rewrite (U_atom E 33 SB H33) by (unfold SB; lia); reflexivity).
assert (UX : U E (SOff 32 0) = Xv) by (apply U_atom; [exact H32 | lia]).
assert (UY : U E (SOff 34 0) = Yv) by (apply U_atom; [exact H34 | lia]).
unfold sh_ok, rcf_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
 unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite UB; rewrite <- (aview_rd_of SEGS); split.
- rewrite UX. apply (tbl_addr lyc Sc Wc memc mdc k); [exact HJ | lia | lia].
- rewrite UX. change (Z.min 4 12) with 4. change (Z.max 4 12) with 12. intros a Ha.
  destruct (tbl_bounds a ltac:(lia)) as (_ & _ & Hs). unfold SHADOW_OFF, kLowShadowBeg, kHighShadowEnd in *. lia.
- rewrite UY. apply (tbl_addr lyc Sc Wc memc mdc k); [exact HJ | lia | lia].
- rewrite UY. change (Z.min 0 8) with 0. change (Z.max 0 8) with 8. intros a Ha.
  destruct (tbl_bounds a ltac:(lia)) as (_ & _ & Hs). unfold SHADOW_OFF, kLowShadowBeg, kHighShadowEnd in *. lia.
Qed.
(* the argument slots of the table hold their entry values; they are no nargs field *)
Lemma slot_not_nargs : forall i a b, (i < NE)%nat -> (a < nP i)%nat -> YA i a <= b < YA i a + 8 -> ~ PRcf.nargs_field c NE b.
Proof.
intros i a b Hi Ha Hb (j & Hj & Hr). pose proof (nP_le6 i Hi) as H6. unfold YA, XE, CALL_SIZE in Hb.
destruct (Nat.le_gt_cases j i) as [Hji|Hji]; nia.
Qed.
Lemma arg_val : forall lyc Sc Wc memc mdc k i a pn, ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 (i < NE)%nat -> nth_error (nth i ps []) a = Some pn -> aval_mem (rdW Wc memc) (YA i a) 8 (fst pn).
Proof.
intros lyc Sc Wc memc mdc k i a pn HJ Hi Ha.
destruct (nth_error ps i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
rewrite (nth_error_nth ps i [] EP) in Ha.
assert (HaP : (a < nP i)%nat) by (rewrite (nth_nP i P EP); apply nth_error_Some; rewrite Ha; discriminate).
destruct (proj2 (proj2 (HSLOT i P EP)) a pn Ha) as [Hv _].
apply (aval_mem_kept (rdW W mem)); [|replace (YA i a) with (c + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a)
  by (unfold YA, XE, CALL_OFF_ARGS; lia); exact Hv].
intros kk Hkk. pose proof (xe_bounds i Hi) as (_ & B2 & B3 & _). pose proof (nP_le6 i Hi).
apply (tbl_keep lyc Sc Wc memc mdc k); [exact HJ | unfold YA, XE, CALL_SIZE in *; lia |].
apply (slot_not_nargs i a); [exact Hi | exact HaP | lia].
Qed.
(* ---------- denotations of the register shapes the runs produce ---------- *)
Lemma den_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite denot_lit_U, H. reflexivity. Qed.
Lemma den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma den_shx_sw : forall E n m o v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v -> 0 <= o -> v + o < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
 sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n o) (SLit 3))) = Z_to_bv 64 (sb + (v + o) / 8).
Proof.
intros E n m o v sb Hn Hm Hv Hc0 Hc Hsb. apply den_of_U.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + o) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + o) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (v + o)) by lia. rewrite (zcanon_small ((v + o) / 8)) by lia. rewrite (zcanon_small sb) by lia. rewrite zcanon_small by lia. lia.
Qed.
Lemma den_shx_inc : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
 sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) (SLit 1)) = Z_to_bv 64 (sb + (v + 8) / 8).
Proof.
intros E n m v sb Hn Hm Hv Hsb. apply den_of_U.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, !U_SLit, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (zcanon 3) 63) with 3. change (zcanon 1) with 1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
replace ((v + 8) / 8) with (v / 8 + 1) by (replace (v + 8) with (v + 1 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
rewrite (zcanon_small v) by lia. rewrite (zcanon_small (v / 8)) by lia. rewrite (zcanon_small sb) by lia.
rewrite (zcanon_small (v / 8 + sb)) by lia. rewrite zcanon_small by lia. lia.
Qed.
Lemma den_s2 : forall E iv cv, ew E 20 = Z_to_bv 64 iv -> ew E 37 = Z_to_bv 64 cv -> 0 <= iv < 2 ^ 20 -> 0 <= cv < 2 ^ 60 ->
 sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 20 0) (SLit 56)) (SLit 60)) (SOff 37 0)) = Z_to_bv 64 (cv + 56 * iv + 60).
Proof.
intros E iv cv H20 H37 Hi Hc. apply den_of_U.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite !U_SOff, !U_SLit, H20, H37. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (zcanon 56) with 56. change (zcanon 60) with 60.
rewrite (zcanon_small iv) by lia. rewrite (zcanon_small cv) by lia.
rewrite (zcanon_small (iv * 56)) by nia. rewrite (zcanon_small (iv * 56 + 60)) by nia. rewrite zcanon_small by nia. lia.
Qed.
Lemma br_lts_lit : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
intros x y Hx Hy. unfold bv_lts. rewrite !YK11.bv_signed_small by (rewrite unsigned_lit_small by lia; lia).
rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
(* a run whose regions have no write window leaves every byte *)
Lemma frame_nowin : forall E (rs : smem) H (m m' : word -> option byte),
 frame_of E rs (mrestrict H m) (mrestrict H m') ->
 (forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo) ->
 forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hw a Ha. apply (kept_of_frame E rs H m m' (fun _ => False) HF); [|exact Ha | tauto].
intros b wlo whi a' Hin Hr. pose proof (Hw b wlo whi Hin). lia.
Qed.

(* ---------- the seeds of the three loop points ---------- *)
Lemma rcf_E2 : forall regs1 Xv Yv Pv NAv, getr regs1 2 = Z_to_bv 64 (sp0 - 112) ->
 bv_unsigned (ew (rcf_E regs1 Xv Yv Pv NAv) 2) = sp0 - 112.
Proof.
intros regs1 Xv Yv Pv NAv H. rewrite (rcf_E_reg regs1 Xv Yv Pv NAv 2 2%bv eq_refl), H.
apply unsigned_lit_small. pose proof rcf_sp0. pose proof asan_consts as (C1 & _). lia.
Qed.
Lemma nargs_mid : forall i a lyc Sc Wc memc mdc, (i < NE)%nat -> rcf_mid i a lyc Sc Wc memc mdc ->
 val_mem SEGS (mrestrict (w_H Wc) memc) (XE i + 4) 4 (Z.of_nat (nP i)).
Proof.
intros i a lyc Sc Wc memc mdc Hi (_ & _ & HNA & _).
destruct (nth_error ps i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
pose proof (HNA i P EP) as HN. rewrite Nat.ltb_irrefl in HN. rewrite <- (nth_nP i P EP) in HN.
apply val_mem_of_aval. replace (XE i + 4) with (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) by (unfold XE, CALL_OFF_NARGS; lia).
exact HN.
Qed.
Lemma seed_O : forall lyc Sc Wc memc mdc regs1 i, (i < NE)%nat -> rcf_mid i 0 lyc Sc Wc memc mdc -> rcf_rb regs1 i ->
 st_ok_pi SEGS VAL (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) rcf_ssO
   (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + (RCF_AF + 0x78))) memc (seg_rom SEGS))) /\
 sh_ok SEGS rcf_Bx rcf_SH (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Wc memc mdc regs1 i Hi MID HR.
pose proof (nargs_mid i 0 lyc Sc Wc memc mdc Hi MID) as HN.
destruct MID as (HJ & _).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof (nP_le6 i Hi) as H6.
destruct (rcf_E_atoms regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) as (E32 & E33 & E34 & E35 & E36 & E37 & ES).
pose proof (rcf_E2 regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i)) (proj1 HR)) as E2.
split.
- rewrite restrict_mkst_fx. unfold rcf_ssO. apply pa_entry_st_ok_full.
  + apply rcf_regs_okO; [exact Hi | unfold XE, CALL_SIZE in *; lia | exact HR].
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    apply (rg_na _ _ (XE i) (Z.of_nat (nP i)) false); [rewrite E32; apply unsigned_lit_small; lia | exact E36 | lia | lia | lia | exact HN | intros; discriminate].
  + cbn. tauto.
  + apply (rcf_facts_ok _ (XE i) (XE i + 8) (Z.of_nat (nP i)) E2 E32 E33 E34 E36); unfold XE, CALL_SIZE in *; lia.
- apply (rcf_shok lyc Sc Wc memc mdc (kd i 0) _ (XE i) (XE i + 8) HJ E32 E33 E34); unfold XE, CALL_SIZE in *; lia.
Qed.
Lemma seed_I : forall lyc Sc Wc memc mdc regs1 i a pn, (i < NE)%nat -> nth_error (nth i ps []) a = Some pn ->
 rcf_mid i a lyc Sc Wc memc mdc -> rcf_ri regs1 i a ->
 st_ok_pi SEGS VAL (rcf_E regs1 (XE i) (YA i a) (fst pn) (Z.of_nat (nP i))) rcf_ssI
   (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + (RCF_AF + 0xac))) memc (seg_rom SEGS))) /\
 sh_ok SEGS rcf_Bx rcf_SH (rcf_E regs1 (XE i) (YA i a) (fst pn) (Z.of_nat (nP i))) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Wc memc mdc regs1 i a pn Hi Ha MID HR.
pose proof (nargs_mid i a lyc Sc Wc memc mdc Hi MID) as HN.
destruct MID as (HJ & _).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof (nP_le6 i Hi) as H6.
assert (HaP : (a < nP i)%nat) by (unfold nP; apply nth_error_Some; rewrite Ha; discriminate).
assert (Hpn : In pn (concat ps)).
{ destruct (nth_error ps i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia]. rewrite (nth_error_nth ps i [] EP) in Ha.
  apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact (nth_error_In _ _ Ha)]. }
destruct pn as [p m]. destruct (arg_bounds p m Hpn) as (P1 & P2 & _ & P4 & _).
pose proof (arg_val lyc Sc Wc memc mdc (kd i a) i a (p, m) HJ Hi Ha) as HV. cbn [fst] in HV |- *.
destruct (rcf_E_atoms regs1 (XE i) (YA i a) p (Z.of_nat (nP i))) as (E32 & E33 & E34 & E35 & E36 & E37 & ES).
pose proof (rcf_E2 regs1 (XE i) (YA i a) p (Z.of_nat (nP i)) (proj1 (proj1 (proj1 HR)))) as E2.
assert (HY : XE i + 8 <= YA i a /\ YA i a + 8 <= XE i + 56) by (unfold YA; lia).
split.
- rewrite restrict_mkst_fx. unfold rcf_ssI. apply pa_entry_st_ok_full.
  + apply rcf_regs_okI; [exact Hi | exact HaP | exact HR].
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (rg_na _ _ (XE i) (Z.of_nat (nP i)) false); [rewrite E32; apply unsigned_lit_small; lia | exact E36 | lia | lia | lia | exact HN | intros; discriminate].
    * assert (Rq : 0 < req_size m) by (apply req_size_pos0; exact P4).
      apply (rg_arg _ _ (YA i a) p); [rewrite E34; apply unsigned_lit_small; lia | exact E35 | lia | lia | lia | apply val_mem_of_aval; exact HV].
  + apply pairwise_disjoint_of_extents. unfold rcf_na, rcf_arg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite E32, E34, !unsigned_lit_small by lia. lia.
  + apply (rcf_facts_ok _ (XE i) (YA i a) (Z.of_nat (nP i)) E2 E32 E33 E34 E36); unfold YA, XE, CALL_SIZE in *; lia.
- apply (rcf_shok lyc Sc Wc memc mdc (kd i a) _ (XE i) (YA i a) HJ E32 E33 E34); unfold YA, XE, CALL_SIZE in *; lia.
Qed.
Lemma seed_T : forall lyc Sc Wc memc mdc regs1 i, (i < NE)%nat -> rcf_mid i (nP i) lyc Sc Wc memc mdc -> rcf_rt regs1 i ->
 st_ok_pi SEGS VAL (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) rcf_ssT
   (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + (RCF_AF + 0xe8))) memc (seg_rom SEGS))) /\
 sh_ok SEGS rcf_Bx rcf_SH (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Wc memc mdc regs1 i Hi MID HR.
pose proof (nargs_mid i (nP i) lyc Sc Wc memc mdc Hi MID) as HN.
destruct MID as (HJ & (FRc & FRs) & _).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof (nP_le6 i Hi) as H6.
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
destruct (rcf_E_atoms regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) as (E32 & E33 & E34 & E35 & E36 & E37 & ES).
pose proof (rcf_E2 regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i)) (proj1 (proj1 HR))) as E2.
split.
- rewrite restrict_mkst_fx. unfold rcf_ssT. apply pa_entry_st_ok_full.
  + apply rcf_regs_okT; [exact Hi | unfold XE, CALL_SIZE in *; lia | exact HR].
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (rg_stk _ _ (sp0 - 112) E2 E37); [lia | exact ES | lia | lia | apply val_mem_of_aval; exact FRc |].
      intros j r Hj. apply val_mem_of_aval. exact (FRs j r Hj).
    * apply (rg_na _ _ (XE i) (Z.of_nat (nP i)) true); [rewrite E32; apply unsigned_lit_small; lia | exact E36 | lia | lia | lia | exact HN |].
      intros _ o Ho. apply (tbl_wr lyc Sc Wc memc mdc (kd i (nP i))); [exact HJ | unfold XE, CALL_SIZE in *; lia].
  + apply pairwise_disjoint_of_extents. unfold rcf_stk, rcf_na, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite E2, E32, !unsigned_lit_small by lia. lia.
  + apply (rcf_facts_ok _ (XE i) (XE i + 8) (Z.of_nat (nP i)) E2 E32 E33 E34 E36); unfold XE, CALL_SIZE in *; lia.
- apply (rcf_shok lyc Sc Wc memc mdc (kd i (nP i)) _ (XE i) (XE i + 8) HJ E32 E33 E34); unfold XE, CALL_SIZE in *; lia.
Qed.
(* ---------- the runs ---------- *)
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Ltac awr_ro := lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc fr lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac nowin := let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let Hin := fresh "Hin" in
  intros b wlo whi Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia|]); destruct Hin.
Ltac rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
(* the registers of rcf_rb, from a state that keeps them in the loop points' shapes *)
Ltac rb_tac HS XR X32 X33 R2 R3 R4 R8 R20 :=
 split; [rreg HS; rewrite den_atom0, (XR 2%nat 2%bv eq_refl); exact R2|];
 split; [rreg HS; rewrite den_atom0, (XR 3%nat 3%bv eq_refl); exact R3|];
 split; [rreg HS; rewrite den_atom0, (XR 4%nat 4%bv eq_refl); exact R4|];
 split; [rreg HS; rewrite den_atom0, (XR 8%nat 8%bv eq_refl); exact R8|];
 split; [rreg HS; rewrite den_atom0, (XR 20%nat 20%bv eq_refl); exact R20|];
 split; [rreg HS; rewrite (den_off _ 33 SB 0 X33), Z.add_0_r by (unfold SB; lia); reflexivity|];
 split; [rreg HS; apply (den_off _ 32 _ 8 X32); lia|];
 split; [rreg HS; apply (den_off _ 32 _ 8 X32); lia|];
 rreg HS; apply (den_off _ 32 _ 4 X32); lia.
Lemma mid_keep : forall i a a' lyc Sc Wc memc mdc memc' mdc',
 (i < NE)%nat -> rcf_mid i a lyc Sc Wc memc mdc ->
 ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc' mdc' (kd i a) ->
 (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memc' x = rdW Wc memc x) ->
 rdone i a' = rdone i a -> rcf_mid i a' lyc Sc Wc memc' mdc'.
Proof.
intros i a a' lyc Sc Wc memc mdc memc' mdc' Hi (_ & (FRc & FRs) & HNA & HPERM & HMO) HJ K Hd.
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
unfold rcf_mid, kd. rewrite Hd. fold (kd i a). split; [exact HJ|]. split; [split|]. 
- apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply K; lia | exact FRc].
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- rcf_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply K; lia | exact (FRs j r Hj)].
- split; [|split; [exact HPERM | exact HMO]].
  intros j P Hj. assert (HjN : (j < NE)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  pose proof (xe_bounds j HjN) as (B1 & B2 & B3 & B4 & B5).
  apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply K; unfold XE, CALL_SIZE, CALL_OFF_NARGS in *; lia | exact (HNA j P Hj)].
Qed.
Lemma outer_ok : forall i, ST_T i -> ((0 < nP i)%nat -> ST_I i 0) -> ST_O i.
Proof.
intros i HT HI lyc Sc Wc memc mdc regs1 Hi MID HR.
destruct (seed_O lyc Sc Wc memc mdc regs1 i Hi MID HR) as [HS SHOK].
pose proof MID as (HJ & _).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof (nP_le6 i Hi) as H6.
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
destruct (rcf_E_atoms regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) as (E32 & E33 & E34 & E35 & E36 & E37 & ES).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) n = getr regs1 r)
  by (intros; apply rcf_E_reg; assumption).
assert (HEI : img_env VAL A_LIM (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i)))) by apply Eimg_env.
destruct HR as (R2 & R3 & R4 & R8 & R20 & R21 & R9 & R23 & R18).
unfold cfgA.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ro. }
pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* blez taken: the entry has no argument *)
  assert (HnP : nP i = 0%nat).
  { cbn [branch_taken sv_denot] in Hc. rewrite E36, unsigned_lit_small, Z.add_0_r in Hc by lia.
    rewrite br_lts_lit in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (RCF_AF + 0xe8).
  { awr_ro. }
  pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K2. clear HF HFr HG.
  pmkst HS. unfold ST_T, cfgA in HT. apply (HT lyc Sc); [exact Hi | |].
  + rewrite HnP. apply (mid_keep i 0 0 lyc Sc Wc memc mdc _ _ Hi MID HJ); [|reflexivity].
    intros x Hx. rewrite K2, K1 by exact Hx. reflexivity.
  + split; [|rreg HS; apply (denot_shx _ 32 33 4 (XE i) SB E32 E33); unfold SB; lia].
    rb_tac HS EE E32 E33 R2 R3 R4 R8 R20.
- (* blez not taken: the first argument *)
  assert (HnP : (0 < nP i)%nat).
  { cbn [branch_taken sv_denot] in Hc. rewrite E36, unsigned_lit_small, Z.add_0_r in Hc by lia.
    rewrite br_lts_lit in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (RCF_AF + 0xac).
  { awr_ro. }
  pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K2. clear HF HFr HG.
  pmkst HS. specialize (HI HnP). unfold ST_I, cfgA in HI. apply (HI lyc Sc); [exact Hi | exact HnP | |].
  + apply (mid_keep i 0 0 lyc Sc Wc memc mdc _ _ Hi MID HJ); [|reflexivity].
    intros x Hx. rewrite K2, K1 by exact Hx. reflexivity.
  + unfold rcf_ri, rcf_rt. replace (YA i 0) with (XE i + 8) by (unfold YA; lia).
    split; [split; [rb_tac HS EE E32 E33 R2 R3 R4 R8 R20 | rreg HS; apply (denot_shx _ 32 33 4 (XE i) SB E32 E33); unfold SB; lia]|].
    split; [rreg HS; apply (den_shx_sw _ 32 33 8 (XE i) SB E32 E33); unfold SB; lia|].
    split; [rreg HS; apply (den_off _ 32 (XE i) 8 E32); lia|].
    split; [rreg HS; apply (den_off _ 32 (XE i) 8 E32); lia|].
    rreg HS. reflexivity.
Qed.
(* ---------- the arguments freed so far ---------- *)
Lemma concat_split : forall i a pn, (i < NE)%nat -> nth_error (nth i ps []) a = Some pn ->
 exists rest, concat ps = rdone i a ++ pn :: rest.
Proof.
intros i a pn Hi Ha. unfold rdone.
destruct (nth_error ps i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
rewrite (nth_error_nth ps i [] EP) in Ha |- *.
destruct (nth_error_split ps i EP) as (l1 & l2 & Eps & Hl1).
destruct (nth_error_split P a Ha) as (q1 & q2 & EP' & Hq1).
exists (q2 ++ concat l2). rewrite Eps, concat_app. cbn [concat]. rewrite EP'.
rewrite <- Hl1, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
rewrite <- Hq1, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
rewrite <- !app_assoc. reflexivity.
Qed.
Lemma pn_not_done : forall i a pn, (i < NE)%nat -> nth_error (nth i ps []) a = Some pn -> ~ In pn (rdone i a).
Proof.
intros i a pn Hi Ha Hin. destruct (concat_split i a pn Hi Ha) as (rest & E). pose proof HNODUP as ND. rewrite E in ND.
apply (rcfr_fst_disj (rdone i a) (pn :: rest) pn ND Hin). left. reflexivity.
Qed.
Lemma kd_lt : forall i a pn, (i < NE)%nat -> nth_error (nth i ps []) a = Some pn -> kd i a + 1 <= Z.of_nat (length (concat ps)).
Proof.
intros i a pn Hi Ha. destruct (concat_split i a pn Hi Ha) as (rest & E). unfold kd. rewrite E, length_app. cbn [length]. lia.
Qed.
Lemma firstn_snoc : forall {A} (l : list A) a x, nth_error l a = Some x -> firstn (Datatypes.S a) l = firstn a l ++ [x].
Proof.
intros A l. induction l as [|y l IH]; intros [|a] x H; cbn in H; try discriminate.
- injection H as <-. reflexivity.
- cbn [firstn app]. rewrite (IH a x H). reflexivity.
Qed.
Lemma rdone_S : forall i a pn, (i < NE)%nat -> nth_error (nth i ps []) a = Some pn -> rdone i (Datatypes.S a) = rdone i a ++ [pn].
Proof.
intros i a pn Hi Ha. unfold rdone. rewrite <- app_assoc. f_equal. exact (firstn_snoc _ a pn Ha).
Qed.
Lemma rdone_next : forall i, (i < NE)%nat -> rdone (Datatypes.S i) 0 = rdone i (nP i).
Proof.
intros i Hi. unfold rdone, nP. rewrite firstn_O, app_nil_r.
destruct (nth_error ps i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
rewrite (nth_error_nth ps i [] EP), firstn_all, (firstn_snoc ps i P EP), concat_app. cbn [concat]. rewrite app_nil_r. reflexivity.
Qed.
Lemma rdone_all : forall i, Datatypes.S i = NE -> rdone i (nP i) = concat ps.
Proof.
intros i Hi. rewrite <- (rdone_next i ltac:(lia)). unfold rdone. rewrite Hi, firstn_all, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma perm_free : forall (bl0 bl bl' l1 l2 d : list (Z * Z)) (pn : Z * Z), Permutation bl0 (bl ++ d) -> bl = l1 ++ pn :: l2 -> bl' = l1 ++ l2 ->
 Permutation bl0 (bl' ++ (d ++ [pn])).
Proof.
intros bl0 bl bl' l1 l2 d pn HP -> ->. eapply Permutation_trans; [exact HP|].
rewrite <- app_assoc. cbn [app]. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
replace (pn :: l1 ++ l2 ++ d) with ([pn] ++ ((l1 ++ l2) ++ d)) by (rewrite <- app_assoc; reflexivity).
replace ((l1 ++ l2) ++ d ++ [pn]) with (((l1 ++ l2) ++ d) ++ [pn]) by (rewrite <- app_assoc; reflexivity).
apply Permutation_app_comm.
Qed.
(* across the free: the frame and the table are kept *)
Lemma call_kept_rel : forall lyc Sc Wc memc mdc k memT W2 mem2 (Er : Z -> Prop) a,
 ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
 acall_kept SEGS B lyc Sc Wc memT W2 mem2 (sp0 + -112 - ASTACK) (sp0 + -112) Er ->
 (forall x, c <= x < c + tbl_n -> ~ Er x) ->
 (sp0 - 112 <= a < sp0 \/ c <= a < c + tbl_n) -> rdW W2 mem2 a = rdW Wc memT a.
Proof.
intros lyc Sc Wc memc mdc k memT W2 mem2 Er a HJ (K1 & K2 & K3 & K4 & _) HEr Ha.
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
destruct Ha as [Ha | Ha].
- apply K1; [lia | lia].
- destruct rcf_home_split as [HP | HF].
  + destruct (pg_prog a (HP a Ha)) as (_ & Ho & He). exact (K3 a (cif_prog_img a (HP a Ha)) Ho He).
  + destruct HF as (cid & pos & Hfin & _ & _ & Hlo & Hhi & _).
    destruct (jr_frames lyc Sc Wc memc mdc k HJ) as [Efr Efa].
    apply (K4 cid pos a); [rewrite Efr; exact Hfin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa; unfold tbl_n in *; lia | exact (HEr a Ha)].
Qed.
Lemma tbl_not_blk : forall pn x, In pn (concat ps) -> c <= x < c + tbl_n -> ~ (fst pn <= x < fst pn + req_size (snd pn)).
Proof. intros [p m] x Hin Hx Hr. exact (tbl_arg_apart p m x Hin Hr Hx). Qed.
Lemma mid_call : forall i a pn lyc Sc Wc memc mdc memT ly2 S2 W2 mem2 mem3 md3 l1 l2,
 (i < NE)%nat -> nth_error (nth i ps []) a = Some pn ->
 rcf_mid i a lyc Sc Wc memc mdc ->
 (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memT x = rdW Wc memc x) ->
 acall_kept SEGS B lyc Sc Wc memT W2 mem2 (sp0 + -112 - ASTACK) (sp0 + -112) (fun x => fst pn <= x < fst pn + req_size (snd pn)) ->
 ablocks B lyc Sc = l1 ++ pn :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
 mo_le MT Sc S2 (mo_free MT) ->
 (forall x, 0 <= x < 2 ^ 64 -> rdW W2 mem3 x = rdW W2 mem2 x) ->
 ajournal SEGS B STK sp0 FP ly S W mem md [] ly2 S2 W2 mem3 md3 (kd i a + 1) ->
 rcf_mid i (Datatypes.S a) ly2 S2 W2 mem3 md3.
Proof.
intros i a pn lyc Sc Wc memc mdc memT ly2 S2 W2 mem2 mem3 md3 l1 l2 Hi Ha MID K1 HK Ebl Ebl2 MLE K3 HJ3.
destruct MID as (HJ & (FRc & FRs) & HNA & HPERM & HMO).
assert (Hpn : In pn (concat ps)).
{ destruct (concat_split i a pn Hi Ha) as (rest & E). rewrite E. apply in_or_app. right. left. reflexivity. }
pose proof rcf_sp0 as (S1 & S2' & S3). pose proof asan_consts as (C1 & _).
assert (KK : forall x, sp0 - 112 <= x < sp0 \/ c <= x < c + tbl_n -> rdW W2 mem3 x = rdW Wc memc x).
{ intros x Hx. assert (Hx64 : 0 <= x < 2 ^ 64).
  { destruct Hx as [Hx | Hx]; [lia|]. destruct (tbl_bounds x Hx) as (T1 & T2 & _). lia. }
  rewrite (K3 x Hx64), (call_kept_rel lyc Sc Wc memc mdc (kd i a) memT W2 mem2 _ x HJ HK (fun y Hy => tbl_not_blk pn y Hpn Hy) Hx).
  exact (K1 x Hx64). }
unfold rcf_mid, kd. rewrite (rdone_S i a pn Hi Ha), length_app. cbn [length].
replace (Z.of_nat (length (rdone i a) + 1)) with (kd i a + 1) by (unfold kd; lia).
split; [exact HJ3|]. split; [split|].
- apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply KK; lia | exact FRc].
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- rcf_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply KK; lia | exact (FRs j r Hj)].
- split; [|split].
  + intros j P Hj. assert (HjN : (j < NE)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    pose proof (xe_bounds j HjN) as (B1 & B2 & B3 & B4 & B5).
    apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply KK; right; unfold XE, CALL_SIZE, CALL_OFF_NARGS in *; lia | exact (HNA j P Hj)].
  + exact (perm_free (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly2 S2) l1 l2 (rdone i a) pn HPERM Ebl Ebl2).
  + replace ((kd i a + 1) * mo_free MT) with (kd i a * mo_free MT + mo_free MT) by lia.
    exact (mo_le_trans MT MTL _ _ _ _ _ HMO MLE).
Qed.
Ltac clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* INNER: free argument a of entry i, then reload nargs and loop or leave *)
Lemma inner_ok : forall i a, ST_T i -> ((Datatypes.S a < nP i)%nat -> ST_I i (Datatypes.S a)) -> ST_I i a.
Proof.
intros i a HT HI lyc Sc Wc memc mdc regs1 Hi Ha MID HR.
destruct (nth_error (nth i ps []) a) as [pn|] eqn:Epn; [|apply nth_error_None in Epn; unfold nP in Ha; lia].
destruct (seed_I lyc Sc Wc memc mdc regs1 i a pn Hi Epn MID HR) as [HS SHOK].
pose proof MID as (HJ & _ & _ & HPERM & HMO). pose proof HJ as HJ0.
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof (nP_le6 i Hi) as H6.
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
pose proof (pa_base_lo (L := cmd_listing)) as HBLO. pose proof (@pa_B_ok _ _ PI) as HBASE.
assert (Hpn : In pn (concat ps)) by (destruct (concat_split i a pn Hi Epn) as (rest & E); rewrite E; apply in_or_app; right; left; reflexivity).
assert (Hpn2 : In (fst pn, snd pn) (concat ps)) by (destruct pn; exact Hpn).
destruct (arg_bounds (fst pn) (snd pn) Hpn2) as (P1 & P2 & _ & P4 & _).
assert (Rq : 0 < req_size (snd pn)) by (apply req_size_pos0; exact P4).
destruct (rcf_E_atoms regs1 (XE i) (YA i a) (fst pn) (Z.of_nat (nP i))) as (E32 & E33 & E34 & E35 & E36 & E37 & ES).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 (XE i) (YA i a) (fst pn) (Z.of_nat (nP i))) n = getr regs1 r)
  by (intros; apply rcf_E_reg; assumption).
assert (HEI : img_env VAL A_LIM (rcf_E regs1 (XE i) (YA i a) (fst pn) (Z.of_nat (nP i)))) by apply Eimg_env.
destruct HR as (((R2 & R3 & R4 & R8 & R20 & R21 & R9 & R23 & R18) & R24) & R26 & R22 & R19 & R25).
assert (HY : XE i + 8 <= YA i a /\ YA i a + 8 <= XE i + 56) by (unfold YA; lia).
pose proof HPRE as (_ & Hra & _ & Hgp & Htp & _).
unfold cfgA.
(* 0x895e8 .. 0x895f4: the argument's shadow, the argument, the free wrapper *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ro. }
pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K1. clear HF HFr HG. clear_md.
pmkst HS. ppcs.
assert (Q2 : getr (ms_regs ms) 2 = Z_to_bv 64 (sp0 - 112)) by (rreg HS; rewrite den_atom0, (EE 2%nat 2%bv eq_refl); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rreg HS; rewrite den_atom0, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rreg HS; rewrite den_atom0, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (Q8 : getr (ms_regs ms) 8 = Z_to_bv 64 (Z.of_nat NE)) by (rreg HS; rewrite den_atom0, (EE 8%nat 8%bv eq_refl); exact R8).
assert (Q10 : getr (ms_regs ms) 10 = w64 (fst pn)) by (rreg HS; rewrite (den_off _ 35 (fst pn) 0 E35), Z.add_0_r by lia; reflexivity).
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (RCF_AF + 0xbc))) by (rreg HS; exact (codeptr_val _ 12564 HEI)).
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) Wc (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W mem md [] lyc Sc _ (kd i a)
    (fst pn) (snd pn) (-112) (Z_to_bv 64 (BASE + (RCF_AF + 0xbc))) [] HJ).
  - pose proof (Permutation_in _ HPERM (arg_live pn Hpn)) as Hin. apply in_app_or in Hin as [Hin | Hin];
      [destruct pn; exact Hin | exfalso; exact (pn_not_done i a pn Hi Epn Hin)].
  - exact Q10.
  - unfold spZ at 1. rewrite Q2, unsigned_lit_small by lia. lia.
  - reflexivity.
  - lia.
  - rewrite rcf_STK. unfold ASTACK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold RCF_AF, AF_rec_calls_free; lia | reflexivity].
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). pose proof (kd_lt i a pn Hi Epn).
    unfold EV_REC_CALLS_FREE in HEV. lia.
  - apply (achain_chain_pre lyc _ (spZ (ms_regs ms)) (Z.of_nat NE) [] (ms_regs ms)).
    + apply achain_low. lia.
    + unfold spZ. rewrite Q2, unsigned_lit_small by lia. lia.
    + unfold s0Z. rewrite Q8, unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite Q1. unfold RCF_AF, AF_rec_calls_free. rewrite unsigned_lit_small by lia. lia.
  - intros _ j Hj. destruct pn as [p m]. exact (fp_block p m j Hpn Hj).
  - apply (mok_station MT S Sc (XM_REC_CALLS_FREE MT ps) (kd i a * mo_free MT) (mo_free MT) MTL HMOK HMO (mo_free_nonneg MT MTL)).
    pose proof (kd_lt i a pn Hi Epn). pose proof (mo_free_nonneg MT MTL). unfold XM_REC_CALLS_FREE. nia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2' & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfrs2 & HK & MLE & HJt).
rewrite <- (surjective_pairing pn) in Ebl.
(* back at 0x895f8 *)
jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E32, unsigned_lit_small by lia; intros x Hx; [|lia].
  apply (mbyte_of_aview SEGS).
  apply (call_kept_rel lyc Sc Wc memc mdc (kd i a) (ms_mem ms) W2 mem2 _ x HJ0 HK (fun y Hy => tbl_not_blk pn y Hpn Hy)).
  right. unfold XE, CALL_SIZE in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc (rcf_E regs1 (XE i) (YA i a) (fst pn) (Z.of_nat (nP i))) 64 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 64)%nat -> ew E2 n = ew (rcf_E regs1 (XE i) (YA i a) (fst pn) (Z.of_nat (nP i))) n)
  by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
clear HE2.
assert (F32 : ew E2 32 = Z_to_bv 64 (XE i)) by (rewrite OLD by lia; exact E32).
assert (F33 : ew E2 33 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact E33).
assert (F34 : ew E2 34 = Z_to_bv 64 (YA i a)) by (rewrite OLD by lia; exact E34).
assert (F36 : ew E2 36 = Z_to_bv 64 (Z.of_nat (nP i))) by (rewrite OLD by lia; exact E36).
assert (XR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite OLD by lia. apply EE. exact Hn. }
assert (F25 : ew E2 25 = Z_to_bv 64 (Z.of_nat a)) by (rewrite (XR 25%nat 25%bv eq_refl); exact R25).
assert (SHOK2 : sh_ok SEGS rcf_Bx rcf_SH E2 (mrestrict (w_H W2) mem2))
  by (apply (rcf_shok ly2 S2' W2 mem2 md2 (kd i a + 1) E2 (XE i) (YA i a) HJ2 F32 F33 F34); unfold XE, CALL_SIZE in *; lia).
change (BASE + (RCF_AF + 0xbc)) with (BASE + 12564).
(* 0x895f8 .. 0x89614: the nargs shadow and reload, the counters, blt *)
paj_run_tok RUN HS HJ2 SHOK2 Bspan.
{ awr_ro. }
pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K2. clear HF HFr HG. clear_md.
psrr_branch_tok RUN BR HS SHOK2 Bspan.
- (* blt taken: the next argument *)
  assert (HaS : (Datatypes.S a < nP i)%nat).
  { cbn [branch_taken] in Hc. rewrite (den_off _ 25 _ 1 F25), (den_off _ 36 _ 0 F36), Z.add_0_r in Hc by lia.
    rewrite br_lts_lit in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ2 SHOK2 Bspan (RCF_AF + 0xac).
  { awr_ro. }
  pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K3. clear HF HFr HG. clear_md.
  pmkst HS. specialize (HI HaS). unfold ST_I, cfgA in HI. apply (HI ly2 S2'); [exact Hi | exact HaS | |].
  + apply (mid_call i a pn lyc Sc Wc memc mdc (ms_mem ms) ly2 S2' W2 mem2 _ _ l1 l2 Hi Epn MID K1 HK Ebl Ebl2 MLE); [|exact HJ2].
    intros x Hx. rewrite K3, K2 by exact Hx. reflexivity.
  + unfold rcf_ri, rcf_rt. replace (YA i (Datatypes.S a)) with (YA i a + 8) by (unfold YA; lia).
    split; [split; [rb_tac HS XR F32 F33 R2 R3 R4 R8 R20 | rreg HS; apply (denot_shx _ 32 33 4 (XE i) SB F32 F33); unfold SB; lia]|].
    split; [rreg HS; apply (den_shx_inc _ 34 33 (YA i a) SB F34 F33); unfold SB; lia|].
    split; [rreg HS; apply (den_off _ 34 (YA i a) 8 F34); lia|].
    split; [rreg HS; apply (den_off _ 34 (YA i a) 8 F34); lia|].
    rreg HS. rewrite (den_off _ 25 (Z.of_nat a) 1 F25) by lia. f_equal. lia.
- (* blt not taken: the last argument freed *)
  assert (HaS : Datatypes.S a = nP i).
  { cbn [branch_taken] in Hc. rewrite (den_off _ 25 _ 1 F25), (den_off _ 36 _ 0 F36), Z.add_0_r in Hc by lia.
    rewrite br_lts_lit in Hc by lia. apply Z.ltb_ge in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ2 SHOK2 Bspan (RCF_AF + 0xe8).
  { awr_ro. }
  pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K3. clear HF HFr HG. clear_md.
  pmkst HS. unfold ST_T, cfgA in HT. apply (HT ly2 S2'); [exact Hi | |].
  + rewrite <- HaS. apply (mid_call i a pn lyc Sc Wc memc mdc (ms_mem ms) ly2 S2' W2 mem2 _ _ l1 l2 Hi Epn MID K1 HK Ebl Ebl2 MLE); [|exact HJ2].
    intros x Hx. rewrite K3, K2 by exact Hx. reflexivity.
  + split; [rb_tac HS XR F32 F33 R2 R3 R4 R8 R20 | rreg HS; apply (denot_shx _ 32 33 4 (XE i) SB F32 F33); unfold SB; lia].
Qed.
(* ---------- the post at the return ---------- *)
Lemma pw_nodup : forall (l : list (Z * Z)), Forall (fun b => 0 <= snd b) l ->
 pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hn H; [constructor|]. cbn [map pairwise] in H. destruct H as [Hf Hp].
apply Forall_cons_iff in Hn as [Hx Hn]. constructor; [|exact (IH Hn Hp)].
intros Hin. apply (in_map (fun b => (fst b, req_size (snd b)))) in Hin. rewrite Forall_forall in Hf.
pose proof (Hf _ Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos0 (snd x) Hx). lia.
Qed.
Lemma ablocks_nodup : List.NoDup (ablocks B ly S).
Proof.
destruct (al_sep _ _ LAWS ly S W mem md (proj1 rcf_pre)) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply (pw_nodup _); [|exact Hp]. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n (proj1 rcf_pre) Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
Qed.
Lemma inrec_cmdPG : forall a, rcf_inrec a -> inFP cmd_PG a.
Proof.
intros a [H | H].
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in H; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in H; lia].
Qed.
Lemma pg_keep : forall ly' S' (W' : world SEGS) mem' md' k a, ajournal SEGS B STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k ->
 inFP cmd_PG a -> ~ PRcf.nargs_field c NE a -> rdW W' mem' a = rdW W mem a.
Proof.
intros ly' S' W' mem' md' k a HJ Ha Hn. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (pg_prog a Ha) as (_ & Ho & He). apply F3; [exact (cif_prog_img a Ha) | exact Ho | exact He |].
apply (fp_spares_closed FP a fp_closed). intros Hf. destruct (fp_cases a Hf) as [H | (p & m & Hin & Hr)]; [exact (Hn H)|].
exact (proj2 (proj2 (proj2 (proj2 (arg_bounds p m Hin)))) a Hr (cif_prog_img a Ha)).
Qed.
Lemma blk_keep : forall ly' S' (W' : world SEGS) mem' md' k p n i, ajournal SEGS B STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k ->
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) -> In (p, n) (ablocks B ly' S') -> 0 <= i < n ->
 rdW W' mem' (p + i) = rdW W mem (p + i).
Proof.
intros ly' S' W' mem' md' k p n i HJ HP Hin Hi. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hin0 : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
destruct (al_blocks _ _ LAWS ly S W mem md p n (proj1 rcf_pre) Hin0) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos0 n ltac:(lia)) as [Hq1 Hq2].
apply (F2 p n i Hin0 Hin); [lia|]. intros Hf. destruct (fp_cases _ Hf) as [(j & Hj & Hr) | (q & m & Hq & Hr)].
- assert (Ht : c <= p + i < c + tbl_n) by (unfold tbl_n, CALL_SIZE in *; nia).
  destruct rcf_home_split as [HPG | HF].
  + exact (blk_img SEGS B LAWS ly S W mem md p n (p + i) (proj1 rcf_pre) Hin0 ltac:(lia) (cif_prog_img _ (HPG _ Ht))).
  + destruct HF as (cid & pos & Hfin & _ & _ & Hlo & Hhi & _).
    pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n cid pos (proj1 rcf_pre) Hin0 Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold tbl_n in *. lia.
- pose proof (arg_live _ Hq) as Hq0.
  assert (Hdec : (q, m) = (p, n) \/ (q, m) <> (p, n))
    by (destruct (Z.eq_dec q p), (Z.eq_dec m n); [left; congruence | right; congruence | right; congruence | right; congruence]).
  destruct Hdec as [Eq | Ne].
  + rewrite Eq in Hq. pose proof (Permutation_NoDup HP ablocks_nodup) as ND. apply NoDup_ListNoDup in ND.
    exact (rcfr_nodup_disj _ _ _ (p, n) ND Hin Hq).
  + pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n (proj1 rcf_pre) Hq0 Hin0 Ne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma rcf_Q_ok : forall ly' S' (W' : world SEGS) regs' mem' md' k,
 ajournal SEGS B STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k ->
 (forall i P, nth_error ps i = Some P -> aval_mem (rdW W' mem') (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0) ->
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) ->
 mo_le MT S S' (XM_REC_CALLS_FREE MT ps) ->
 rcf_Q ly' S' W' regs' mem' md'.
Proof.
intros ly' S' W' regs' mem' md' k HJ HNA HP HMO.
assert (HNA' : forall i, (i < NE)%nat -> aval_mem (rdW W' mem') (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0).
{ intros i Hi. destruct (nth_error ps i) as [P|] eqn:EP; [exact (HNA i P EP) | apply nth_error_None in EP; lia]. }
assert (BK : forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i))
  by (intros p n i Hin Hi; exact (blk_keep ly' S' W' mem' md' k p n i HJ HP Hin Hi)).
assert (HBB : blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_FREE).
{ rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly S), (YCbq.bsum_perm _ _ HP), YCbq.bsum_app.
  unfold LIVE_REC_CALLS_FREE.
  assert (H0 : forall l : list (Z * Z), (forall p m, In (p, m) l -> 0 <= m) -> 0 <= YCbq.bsum l).
  { induction l as [|[p m] l IH]; intros Hl; [cbn; lia|]. rewrite YCbq.bsum_cons. cbn [snd].
    pose proof (Hl p m (or_introl eq_refl)). pose proof (IH (fun p' m' H => Hl p' m' (or_intror H))). lia. }
  pose proof (H0 (concat ps) (fun p m Hin => proj1 (proj2 (proj2 (proj2 (arg_bounds p m Hin)))))). lia. }
unfold rcf_Q. split; [exact HP|]. split; [exact HNA'|]. split.
{ intros j Hj Hn. apply (tbl_keep ly' S' W' mem' md' k); [exact HJ | unfold tbl_n; lia | exact Hn]. }
split; [exact BK|]. split; [|split; [|split; [|split; [exact HBB | exact HMO]]]].
- intros R Q HR Hc Hps. destruct (rcf_rep_grec (ablocks B ly S) (ablocks B ly' S') (rdW W mem) (rdW W' mem') R Q HR) as (Q' & HA & HO).
  + intros a Ha Hn. apply (pg_keep ly' S' W' mem' md' k a HJ (inrec_cmdPG a Ha)). rewrite Hc, Hps. exact Hn.
  + intros i Hi. rewrite <- Hc. apply HNA'. rewrite Hps. exact Hi.
  + rewrite <- Hps. exact HP.
  + exact BK.
  + exists Q'. split; [exact HA | intros pn; exact (HO pn)].
- intros R Q HR Hc Hps. destruct (rcf_rep_spill (ablocks B ly S) (ablocks B ly' S') (rdW W mem) (rdW W' mem') R Q HR) as (Q' & HA & HO).
  + intros a Ha Hn. apply (pg_keep ly' S' W' mem' md' k a HJ (inrec_cmdPG a Ha)). rewrite Hc, Hps. exact Hn.
  + rewrite <- Hc. apply HNA'. rewrite Hps. cbn. lia.
  + rewrite <- Hps. exact HP.
  + exact BK.
  + exists Q'. split; [exact HA | intros pn; exact (HO pn)].
- intros R O HR HA1 HA2 HF. apply (rcf_rep_repA B ly S ly' S' (rdW W mem) (rdW W' mem') R O (concat ps) HR); [| exact HP | exact HF | exact BK].
  intros a Ha. apply (pg_keep ly' S' W' mem' md' k a HJ (inrec_cmdPG a Ha)). intros (j & Hj & Hr).
  destruct Ha as [Ha | Ha]; unfold iv_apart, REC_SIZE, SC_SIZE, CALL_SIZE in *; nia.
Qed.
Lemma post_ok : forall ly' S' (W' : world SEGS) regs' mem' md' k,
 ajournal SEGS B STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k -> k <= EV_REC_CALLS_FREE ps ->
 (forall i P, nth_error ps i = Some P -> aval_mem (rdW W' mem') (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0) ->
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) ->
 mo_le MT S S' (XM_REC_CALLS_FREE MT ps) -> aregs_preserved regs regs' ->
 rcf_post W' (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md').
Proof.
intros ly' S' W' regs' mem' md' k HJ Hk HNA HP HMO HRP. unfold rcf_post, apost_base.
exists ly', S', regs', mem', md'. split; [reflexivity|]. split; [exact (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hk)|].
split; [exact HRP|]. exact (rcf_Q_ok ly' S' W' regs' mem' md' k HJ HNA HP HMO).
Qed.
Lemma frame_win : forall E rs H (m m' : word -> option byte) X, frame_of E rs (mrestrict H m) (mrestrict H m') ->
 ew E 32 = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 ->
 (forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo \/ (b = Some 32%nat /\ wlo = 4 /\ whi = 8)) ->
 forall a, 0 <= a < 2 ^ 64 -> ~ (X + 4 <= a < X + 8) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' X HF HX HXr Hw a Ha Hn. apply (kept_of_frame E rs H m m' (fun a => X + 4 <= a < X + 8) HF); [|exact Ha | exact Hn].
intros b wlo whi a' Hin Hr. destruct (Hw b wlo whi Hin) as [Hl | (-> & -> & ->)]; [lia|].
cbn [base_val] in Hr. rewrite HX, unsigned_lit_small in Hr by lia. lia.
Qed.
Ltac win48 := let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let Hin := fresh "Hin" in
  intros b wlo whi Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; first [left; lia | right; auto] |]); destruct Hin.
Lemma c_range : 0 <= c < 2 ^ 63.
Proof.
pose proof asan_consts as (C1 & _). pose proof tbl_n_nonneg as Hn. unfold tbl_n in Hn.
destruct HHOME as [[H1 H2] | [[H1 H2] | ((cid & pos & Hin & Hc & Hal & Hlo & Hhi) & _ & Hra)]].
- unfold A_G_REC, OFF_CALLS, REC_SIZE in *. lia.
- unfold A_REC_SPILL, SC_SIZE in *. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos (proj1 rcf_pre) Hin) as (F1 & F2 & F3). lia.
Qed.
Ltac awr_tail i HJ E32 Hi :=
  lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc fr lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen with (n := 32%nat) (b := XE i); [reflexivity | rewrite E32; apply unsigned_lit_small; lia | |];
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      apply (tbl_awr _ _ _ _ _ _ a HJ); [lia | apply (fp_nargs i a Hi); unfold XE, CALL_SIZE, CALL_OFF_NARGS in *; lia] |] ].
(* the epilogue 0x89668 .. 0x896a0: every argument freed, every nargs 0 *)
Definition rcf_done lyc Sc (Wc : world SEGS) memc mdc : Prop :=
 ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc (EV_REC_CALLS_FREE ps) /\
 rcf_frame (rdW Wc memc) /\
 (forall j P, nth_error ps j = Some P -> aval_mem (rdW Wc memc) (c + CALL_SIZE * Z.of_nat j + CALL_OFF_NARGS) 4 0) /\
 Permutation (ablocks B ly S) (ablocks B lyc Sc ++ concat ps) /\
 mo_le MT S Sc (XM_REC_CALLS_FREE MT ps).
Definition rcf_ssP : sstate := mkSS (RCF_AF + 0x12c) sr_atoms [rcf_stk] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).
Lemma epi_ok : forall lyc Sc Wc memc mdc regs1, rcf_done lyc Sc Wc memc mdc ->
 getr regs1 2 = Z_to_bv 64 (sp0 - 112) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
 SRr SEGS Wc (cfgA 0x12c regs1 memc mdc) rcf_post.
Proof.
intros lyc Sc Wc memc mdc regs1 (HJ & (FRc & FRs) & HNA & HPERM & HMO) R2 R3 R4.
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
destruct (rcf_E_atoms regs1 0 0 0 0) as (E32 & E33 & E34 & E35 & E36 & E37 & ES).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 0 0 0 0) n = getr regs1 r)
  by (intros; apply rcf_E_reg; assumption).
assert (HEI : img_env VAL A_LIM (rcf_E regs1 0 0 0 0)) by apply Eimg_env.
pose proof (rcf_E2 regs1 0 0 0 0 R2) as E2.
assert (HS : st_ok_pi SEGS VAL (rcf_E regs1 0 0 0 0) rcf_ssP
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + (RCF_AF + 0x12c))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcf_ssP. apply pa_entry_st_ok_full.
  + unfold rcf_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    pose proof c_range as Hcr.
    apply (rg_stk _ _ (sp0 - 112) E2 E37); [lia | exact ES | lia | lia | apply val_mem_of_aval; exact FRc |].
    intros j r Hj. apply val_mem_of_aval. exact (FRs j r Hj).
  + cbn. tauto.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2. change (2 ^ 4) with 16. repeat split; try lia. }
assert (SHOK : sh_ok SEGS rcf_Bx [] (rcf_E regs1 0 0 0 0) (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
unfold cfgA.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ro. }
pose proof (frame_nowin _ _ _ _ _ HFr ltac:(nowin)) as K1. clear HF HFr HG. clear_md.
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
pose proof HPRE as (_ & Hra & _).
assert (Q1 : getr (ms_regs ms) 1 = getr regs 1) by (rreg HS; rewrite den_atom0; exact (ES 0%nat 1%nat eq_refl)).
rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra.
apply (post_ok lyc Sc Wc (ms_regs ms) (ms_mem ms) _ (EV_REC_CALLS_FREE ps)).
- apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
- lia.
- intros j P Hj. assert (HjN : (j < NE)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  pose proof (xe_bounds j HjN) as (D1 & D2 & D3 & D4 & D5).
  apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply K1; unfold XE, CALL_SIZE, CALL_OFF_NARGS in *; lia | exact (HNA j P Hj)].
- exact HPERM.
- exact HMO.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr. repeat match type of Hc with _ \/ _ => destruct Hc as [-> | Hc] | ?x = _ => subst x end.
  all: rreg HS.
  all: first
   [ rewrite (den_off _ 2 (sp0 - 112) 112 (eq_trans (EE 2%nat 2%bv eq_refl) R2)) by lia;
     replace (sp0 - 112 + 112) with sp0 by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
   | rewrite den_atom0, (EE 3%nat 3%bv eq_refl), R3; reflexivity
   | rewrite den_atom0, (EE 4%nat 4%bv eq_refl), R4; reflexivity
   | rewrite den_atom0; match goal with |- ew _ ?n = getr regs (Z_to_bv 5 ?r) => exact (ES (n - 38)%nat (Z.to_nat r) eq_refl) end ].
Qed.
(* after the nargs store of entry i *)
Lemma tail_nargs : forall i lyc Sc Wc memc mdc (m2 : word -> option byte), (i < NE)%nat -> rcf_mid i (nP i) lyc Sc Wc memc mdc ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (XE i + 4 <= x < XE i + 8) -> rdW Wc m2 x = rdW Wc memc x) ->
 aval_mem (rdW Wc m2) (XE i + 4) 4 0 ->
 rcf_frame (rdW Wc m2) /\
 (forall j P, nth_error ps j = Some P -> aval_mem (rdW Wc m2) (c + CALL_SIZE * Z.of_nat j + CALL_OFF_NARGS) 4
   (if (j <? Datatypes.S i)%nat then 0 else Z.of_nat (length P))).
Proof.
intros i lyc Sc Wc memc mdc m2 Hi (_ & (FRc & FRs) & HNA & _) K NZ.
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
split; [split|].
- apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply K; lia | exact FRc].
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- rcf_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (aval_mem_kept (rdW Wc memc)); [intros kk Hkk; apply K; lia | exact (FRs j r Hj)].
- intros j P Hj. assert (HjN : (j < NE)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  pose proof (xe_bounds j HjN) as (D1 & D2 & D3 & D4 & D5).
  destruct (Nat.eq_dec j i) as [-> | Hne].
  + rewrite (proj2 (Nat.ltb_lt i (Datatypes.S i)) ltac:(lia)).
    replace (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) with (XE i + 4) by (unfold XE, CALL_OFF_NARGS; lia). exact NZ.
  + pose proof (HNA j P Hj) as H.
    apply (aval_mem_kept (rdW Wc memc)).
    * intros kk Hkk. unfold XE, CALL_SIZE, CALL_OFF_NARGS in *. apply K; lia.
    * destruct (Nat.lt_ge_cases j i) as [Hlt | Hge].
      -- rewrite (proj2 (Nat.ltb_lt j i) Hlt) in H. rewrite (proj2 (Nat.ltb_lt j (Datatypes.S i)) ltac:(lia)). exact H.
      -- rewrite (proj2 (Nat.ltb_ge j i) Hge) in H. rewrite (proj2 (Nat.ltb_ge j (Datatypes.S i)) ltac:(lia)). exact H.
Qed.
Ltac na_of_HS HS NZ E32 X :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r := eval vm_compute in (nth 1 (ss_mem ssx) rcf_arg) in
    let HRg := fresh "HRg" in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg;
    pose proof (field_of_region _ _ 32 X _ 4 8 4 8 4 4%N (SLit 0) 0 HRg) as NZ;
    specialize (NZ ltac:(rewrite E32; apply unsigned_lit_small; lia) ltac:(left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia));
    apply aval_of_val_mem in NZ; clear HRg
  end.
Lemma tail_ok : forall i, ((Datatypes.S i < NE)%nat -> ST_O (Datatypes.S i)) -> ST_T i.
Proof.
intros i HO lyc Sc Wc memc mdc regs1 Hi MID HR.
destruct (seed_T lyc Sc Wc memc mdc regs1 i Hi MID HR) as [HS SHOK].
pose proof MID as (HJ & (FRc & FRs) & HNA & HPERM & HMO).
pose proof (xe_bounds i Hi) as (B1 & B2 & B3 & B4 & B5). pose proof (nP_le6 i Hi) as H6.
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & _).
destruct (rcf_E_atoms regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) as (E32 & E33 & E34 & E35 & E36 & E37 & ES).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) n = getr regs1 r)
  by (intros; apply rcf_E_reg; assumption).
assert (HEI : img_env VAL A_LIM (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i)))) by apply Eimg_env.
destruct HR as ((R2 & R3 & R4 & R8 & R20 & R21 & R9 & R23 & R18) & R24).
assert (E20 : ew (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) 20 = Z_to_bv 64 (Z.of_nat i))
  by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E8 : ew (rcf_E regs1 (XE i) (XE i + 8) 0 (Z.of_nat (nP i))) 8 = Z_to_bv 64 (Z.of_nat NE))
  by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
unfold cfgA.
(* 0x89624 .. 0x8963c: the nargs shadow, the store of 0, the counters, bne *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_tail i HJ E32 Hi. }
pose proof (frame_win _ _ _ _ _ (XE i) HFr E32 ltac:(lia) ltac:(win48)) as K1. clear HF HFr HG. clear_md.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* bne taken: the next entry *)
  assert (HSi : (Datatypes.S i < NE)%nat).
  { rewrite branch_ne_U, !U_SOff, E20, E8, !unsigned_lit_small, !zcanon_small in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (RCF_AF + 0x78).
  { awr_tail i HJ E32 Hi. }
  pose proof (frame_win _ _ _ _ _ (XE i) HFr E32 ltac:(lia) ltac:(win48)) as K2. clear HF HFr HG. clear_md.
  pmkst HS. na_of_HS HS NZ E32 (XE i).
  destruct (tail_nargs i lyc Sc Wc memc mdc _ Hi MID (fun x Hx Hn => eq_trans (K2 x Hx Hn) (K1 x Hx Hn)) NZ) as [FR' NA'].
  unfold ST_O, cfgA in HO. apply (HO HSi lyc Sc); [exact HSi | |].
  + unfold rcf_mid, kd. rewrite (rdone_next i Hi).
    split; [exact HJ|]. split; [exact FR'|]. split; [exact NA'|]. split; [exact HPERM | exact HMO].
  + split; [rreg HS; rewrite den_atom0, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rreg HS; rewrite den_atom0, (EE 3%nat 3%bv eq_refl); exact R3|].
    split; [rreg HS; rewrite den_atom0, (EE 4%nat 4%bv eq_refl); exact R4|].
    split; [rreg HS; rewrite den_atom0; exact E8|].
    split; [rreg HS; rewrite (den_off _ 20 (Z.of_nat i) 1 E20) by lia; f_equal; lia|].
    split; [rreg HS; rewrite (den_off _ 33 SB 0 E33), Z.add_0_r by (unfold SB; lia); reflexivity|].
    split; [rreg HS; rewrite (den_off _ 32 (XE i) 64 E32) by lia; f_equal; unfold XE, CALL_SIZE; lia|].
    split; [rreg HS; rewrite (den_off _ 32 (XE i) 64 E32) by lia; f_equal; unfold XE, CALL_SIZE; lia|].
    rreg HS. rewrite (den_s2 _ (Z.of_nat i) c E20 E37) by lia. f_equal. unfold XE, CALL_SIZE. lia.
- (* bne not taken: the last entry, to the epilogue *)
  assert (HSi : Datatypes.S i = NE).
  { rewrite branch_ne_U, !U_SOff, E20, E8, !unsigned_lit_small, !zcanon_small in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (RCF_AF + 0x12c).
  { awr_tail i HJ E32 Hi. }
  pose proof (frame_win _ _ _ _ _ (XE i) HFr E32 ltac:(lia) ltac:(win48)) as K2. clear HF HFr HG. clear_md.
  pmkst HS. na_of_HS HS NZ E32 (XE i).
  destruct (tail_nargs i lyc Sc Wc memc mdc _ Hi MID (fun x Hx Hn => eq_trans (K2 x Hx Hn) (K1 x Hx Hn)) NZ) as [FR' NA'].
  apply (epi_ok lyc Sc).
  + split; [unfold EV_REC_CALLS_FREE; rewrite <- (rdone_all i HSi); exact HJ|].
    split; [exact FR'|].
    split; [intros j P Hj; pose proof (NA' j P Hj) as H;
      assert (HjN : (j < Datatypes.S i)%nat) by (rewrite HSi; apply nth_error_Some; rewrite Hj; discriminate);
      rewrite (proj2 (Nat.ltb_lt _ _) HjN) in H; exact H|].
    split; [rewrite <- (rdone_all i HSi); exact HPERM|].
    unfold XM_REC_CALLS_FREE. rewrite <- (rdone_all i HSi). exact HMO.
  + rreg HS. rewrite den_atom0, (EE 2%nat 2%bv eq_refl). exact R2.
  + rreg HS. rewrite den_atom0, (EE 3%nat 3%bv eq_refl). exact R3.
  + rreg HS. rewrite den_atom0, (EE 4%nat 4%bv eq_refl). exact R4.
Qed.
Definition rcf_EE : env := Eimg (Ereg regs [w64 SB]).
Lemma rcf_entry_seed :
 st_ok_pi SEGS VAL rcf_EE rcf_ssE (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RCF_AF)) mem (seg_rom SEGS)))
 /\ sh_ok SEGS (SOff 32 0) [] rcf_EE (mrestrict (w_H W) mem).
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := rcf_EE).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; unfold rcf_EE; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; unfold rcf_EE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold rcf_ssE. apply pa_entry_st_ok_full.
- subst E. unfold rcf_EE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite rcf_STK. lia.
  + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
      | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; try lia; exact S3.
Qed.
Lemma frame_stk : forall E rs H (m m' : word -> option byte), frame_of E rs (mrestrict H m) (mrestrict H m') ->
 bv_unsigned (ew E 2) = sp0 ->
 (forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo \/ (b = Some 2%nat /\ wlo = -112 /\ whi = 0)) ->
 forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hsp Hw a Ha Hn. apply (kept_of_frame E rs H m m' (fun a => sp0 - 112 <= a < sp0) HF); [|exact Ha | exact Hn].
intros b wlo whi a' Hin Hr. destruct (Hw b wlo whi Hin) as [Hl | (-> & -> & ->)]; [lia|].
cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
Ltac winstk := let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let Hin := fresh "Hin" in
  intros b wlo whi Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; first [left; lia | right; auto] |]); destruct Hin.
(* the frame the prologue stores: the table pointer at -112, the 13 saved registers above it *)
Lemma entry_frame : forall H (m2 : word -> option byte) cs,
 region_ok SEGS rcf_EE (mrestrict H m2) (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 cs) ->
 In (YP09.mkChunk (-112) (CVal 8 (SOff 10 0))) cs ->
 (forall j r, nth_error rcf_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff r 0))) cs) ->
 rcf_frame (aview SEGS H m2).
Proof.
intros H m2 cs HR Hc Hs.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew rcf_EE n = getr regs r)
  by (intros n r Hn; unfold rcf_EE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew rcf_EE 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pose proof c_range as Hcr.
split.
- apply aval_of_val_mem. replace (sp0 - 112) with (sp0 + -112) by lia. change 8%nat with (N.to_nat 8).
  apply (field_of_region rcf_EE _ 2 sp0 cs (-112) 0 (-112) 0 (-112) 8 (SOff 10 0) c HR Usp Hc).
  + rewrite den_atom0, (EE 10%nat 10%bv eq_refl), H10. reflexivity.
  + cbn. lia.
  + cbn. lia.
- intros j r Hj. assert (Hr27 : (r <= 27)%nat) by (apply nth_error_In in Hj; cbn in Hj; intuition lia).
  apply aval_of_val_mem. replace (sp0 - 112 + (104 - 8 * Z.of_nat j)) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
  change 8%nat with (N.to_nat 8).
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (field_of_region rcf_EE _ 2 sp0 cs (-112) 0 (-112) 0 _ 8 (SOff r 0) _ HR Usp (Hs j r Hj)).
  + rewrite den_atom0, (EE r (Z_to_bv 5 (Z.of_nat r))); [rewrite Z_to_bv_bv_unsigned; reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
  + cbn. lia.
  + cbn. lia.
Qed.
Ltac stk_of_HS HS HRg :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) rcf_arg) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg
  end.
Ltac entry_frame_tac HRg :=
  apply (entry_frame _ _ _ HRg); [vm_compute; repeat first [left; reflexivity | right] |];
  let j := fresh "j" in let r := fresh "r" in let Hr := fresh "Hr" in
  intros j r Hr; do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]);
  cbn in Hr; destruct j; discriminate Hr.
Lemma entry_ok : ((0 < NE)%nat -> ST_O 0) -> SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_free) regs mem md) rcf_post.
Proof.
intros HO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof rcf_sp0 as (S1 & S2 & S3). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof c_range as Hcr.
destruct rcf_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B STK FP ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM rcf_EE) by (unfold rcf_EE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew rcf_EE n = getr regs r)
  by (intros n r Hn; unfold rcf_EE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew rcf_EE 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E2 : ew rcf_EE 2 = Z_to_bv 64 sp0) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E10 : ew rcf_EE 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew rcf_EE 11 = Z_to_bv 64 (Z.of_nat NE)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew rcf_EE 32 = Z_to_bv 64 SB) by (unfold rcf_EE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold cfg_at. change (w64 (BASE + AF_rec_calls_free)) with (Z_to_bv 64 (BASE + RCF_AF)).
(* 0x8953c .. 0x89578: the frame, blez a1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
pose proof (frame_stk _ _ _ _ _ HFr Usp ltac:(winstk)) as K0. clear HF HFr HG. clear_md.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* no entry: to the epilogue *)
  assert (HN0 : NE = 0%nat).
  { cbn [branch_taken sv_denot] in Hc. rewrite E11, unsigned_lit_small, Z.add_0_r in Hc by lia.
    rewrite br_lts_lit in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  assert (Eps : ps = []) by (destruct ps; [reflexivity | discriminate HN0]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (RCF_AF + 0x12c).
  { awr_ok_tac; exact Usp. }
  pose proof (frame_stk _ _ _ _ _ HFr Usp ltac:(winstk)) as K1. clear HF HFr HG. clear_md.
  pmkst HS. stk_of_HS HS HRg.
  apply (epi_ok ly S).
  + split; [replace (EV_REC_CALLS_FREE ps) with 0 by (unfold EV_REC_CALLS_FREE; rewrite Eps; reflexivity); exact HJ|].
    split; [entry_frame_tac HRg|].
    split; [intros j P Hj; rewrite Eps in Hj; destruct j; discriminate Hj|].
    split; [replace (concat ps) with (@nil (Z * Z)) by (rewrite Eps; reflexivity); rewrite app_nil_r; apply Permutation_refl|].
    replace (XM_REC_CALLS_FREE MT ps) with 0 by (unfold XM_REC_CALLS_FREE; rewrite Eps; reflexivity). apply (mo_le_refl MT MTL).
  + rreg HS. rewrite (den_off _ 2 sp0 (-112) E2) by lia. f_equal; lia.
  + rreg HS. rewrite den_atom0. apply EE. reflexivity.
  + rreg HS. rewrite den_atom0. apply EE. reflexivity.
- (* 0x8957c .. 0x895b0: the first entry *)
  assert (HNP : (0 < NE)%nat).
  { cbn [branch_taken sv_denot] in Hc. rewrite E11, unsigned_lit_small, Z.add_0_r in Hc by lia.
    rewrite br_lts_lit in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc. lia. }
  pose proof (xe_bounds 0 HNP) as (B1 & B2 & B3 & B4 & B5).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (RCF_AF + 0x78).
  { awr_ok_tac; exact Usp. }
  pose proof (frame_stk _ _ _ _ _ HFr Usp ltac:(winstk)) as K1. clear HF HFr HG. clear_md.
  pmkst HS. stk_of_HS HS HRg.
  unfold ST_O, cfgA in HO. apply (HO HNP ly S); [exact HNP | |].
  + unfold rcf_mid. change (kd 0 0) with 0. change (rdone 0 0) with (@nil (Z * Z)). rewrite app_nil_r.
    split; [exact HJ|]. split; [entry_frame_tac HRg|].
    split; [|split; [apply Permutation_refl | rewrite Z.mul_0_l; apply (mo_le_refl MT MTL)]].
    intros j P Hj. assert (HjN : (j < NE)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    pose proof (xe_bounds j HjN) as (D1 & D2 & D3 & D4 & D5).
    rewrite (proj2 (Nat.ltb_ge j 0) ltac:(lia)).
    apply (aval_mem_kept (rdW W mem)); [|exact (proj1 (proj2 (HSLOT j P Hj)))].
    intros kk Hkk. unfold XE, CALL_SIZE, CALL_OFF_NARGS in *. rewrite K1, K0 by lia. reflexivity.
  + split; [rreg HS; rewrite (den_off _ 2 sp0 (-112) E2) by lia; f_equal; lia|].
    split; [rreg HS; rewrite den_atom0; apply EE; reflexivity|].
    split; [rreg HS; rewrite den_atom0; apply EE; reflexivity|].
    split; [rreg HS; rewrite den_atom0; exact E11|].
    split; [rreg HS; reflexivity|].
    split; [rreg HS; rewrite den_atom0; exact E32|].
    split; [rreg HS; rewrite (den_off _ 10 c 8 E10) by lia; f_equal; unfold XE; lia|].
    split; [rreg HS; rewrite (den_off _ 10 c 8 E10) by lia; f_equal; unfold XE; lia|].
    rreg HS; rewrite (den_off _ 10 c 4 E10) by lia; f_equal; unfold XE; lia.
Qed.

(* ---------- the loops, by induction on what is left ---------- *)
Lemma all_I : forall i, ST_T i -> forall a, (a < nP i)%nat -> ST_I i a.
Proof.
intros i HT.
assert (G : forall d a, (nP i - a = d)%nat -> (a < nP i)%nat -> ST_I i a).
{ induction d as [|d IH]; intros a Hd Ha; [lia|]. apply inner_ok; [exact HT|]. intros HaS. apply IH; lia. }
intros a Ha. exact (G _ a eq_refl Ha).
Qed.
Lemma all_O : forall i, (i < NE)%nat -> ST_O i.
Proof.
assert (G : forall d i, (NE - i = d)%nat -> (i < NE)%nat -> ST_O i).
{ induction d as [|d IH]; intros i Hd Hi; [lia|].
  assert (HT : ST_T i) by (apply tail_ok; intros HSi; apply IH; lia).
  apply outer_ok; [exact HT|]. intros Hp. exact (all_I i HT 0 Hp). }
intros i Hi. exact (G _ i eq_refl Hi).
Qed.
Lemma rcf_walk : SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_free) regs mem md) rcf_post.
Proof. apply entry_ok. intros Hp. exact (all_O 0 Hp). Qed.
End w.

Theorem trec_calls_free_spec_holds : trec_calls_free_spec B MT.
Proof.
unfold trec_calls_free_spec.
intros ly S W regs mem md ch c ps HPRE HROD H10 H11 HN2 HHOME HSLOT HNODUP HEV HMOK.
eapply rcf_walk; eassumption.
Qed.
End e.
End d.
End b.
