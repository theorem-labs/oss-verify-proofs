(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS4), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Segment 4 of the sweep phase: 0x811f8 -> 0x81298, the group-B loop. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h GrantFrame YC45 GrantACja GrantACjr YC1i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import CtrlIdentityPollBlock.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* The atoms of the turn's three regions are below every atom a call havocs. *)
Ltac gb_ewold := repeat (rewrite ew_havoc_old by (cbv; lia)); reflexivity.

(* ---- why the three comparisons of a turn find equal bytes ---- *)
(* The image's table POLL (object 6, fuzz_grant.c:80-83): the address and size bytes of
   the six identity polls, three bytes each. *)
Definition POLLz : list Z := [0; 0; 4; 6; 0; 8; 16; 0; 17; 16; 17; 9; 17; 0; 17; 17; 17; 9].
(* The compound literal 12 11 05 00 of fuzz_grant.c:355, which the turn writes into the
   frame at F + 544 before it compares. *)
Definition LITz : list Z := [18; 17; 5; 0].

Lemma gb_poll_bytes : forall i j, (i <= 5)%nat -> (j < 3)%nat ->
  nth (3 * i + j) POLLz 0 = nth (20 + j) (GBz (Z.of_nat i)) 0.
Proof.
  intros i j Hi Hj.
  do 6 (destruct i as [|i]; [do 3 (destruct j as [|j]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

Lemma gb_lit_bytes : forall i j, (i <= 5)%nat -> (j < 4)%nat ->
  nth (16 + j) (GBz (Z.of_nat i)) 0 = nth j LITz 0.
Proof.
  intros i j Hi Hj.
  do 6 (destruct i as [|i]; [do 4 (destruct j as [|j]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

Lemma gb_nth_concat34 : forall (L : list (list byte)) k j d,
  Forall (fun r => length r = 34%nat) L -> (k < length L)%nat -> (j < 34)%nat ->
  nth (34 * k + j) (concat L) d = nth j (nth k L []) d.
Proof.
  induction L as [|r L IH]; intros k j d HL Hk Hj; cbn [length] in Hk; [lia|].
  inversion HL as [|r0 L0 Hr HL']; subst r0 L0. cbn [concat].
  destruct k as [|k].
  - cbn [nth]. rewrite app_nth1 by lia. f_equal; lia.
  - rewrite app_nth2 by lia. rewrite Hr. replace (34 * S k + j - 34)%nat with (34 * k + j)%nat by lia.
    cbn [nth]. apply IH; [exact HL' | lia | exact Hj].
Qed.

Lemma gb_nth_unsigned : forall (l : list byte) n,
  nth n (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  induction l as [|b l IH]; intros n; destruct n as [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.

(* Row 5 + i of the sweep is the i-th identity poll row (SweepRowCheck.nth_row_B). *)
Lemma gb_row_bytes : forall pl t i j, ok pl = true -> (i <= 5)%nat -> (j < 34)%nat ->
  nth (34 * (5 + i) + j) (map (fun b : byte => bv_unsigned b) (sw_bytes pl t)) 0 = nth j (GBz (Z.of_nat i)) 0.
Proof.
  intros pl t i j Hok Hi Hj.
  assert (Hw : (1 <= Z.to_nat (sw_in pl))%nat).
  { unfold ok, fits in Hok. unfold sw_in.
    apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _].
    apply Z.leb_le in Hok. lia. }
  unfold sw_bytes. rewrite SWEEP_rows, gb_nth_unsigned.
  pose proof (length_sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t) Hw) as Hlen.
  rewrite gb_nth_concat34;
    [| apply Forall_rowok_len, sweep_rows_ok | lia | exact Hj].
  rewrite nth_row_B by lia. unfold GB, bl.
  rewrite (map_nth (Z_to_bv 8) (GBz (Z.of_nat i)) 0 j).
  apply bv8_small. apply ipb_gbz_range; [lia | exact Hj].
Qed.

(* ---- the symbolic state at the head of the loop ---- *)
(* Atoms 0..31 are the registers at 0x811f8. The regions: the five shadow bytes of
   `poll` (s6 = the frame's shadow base, offsets 58..62), the spill slot 96(s1) that
   holds the compound literal's address (s3 + 80, because s3 = F + 464 and the literal
   is at F + 544), and the literal's four bytes. *)
Definition gb_rs0 : YP09.smem :=
  [ YP09.mkRegion (Some 22%nat) 58 63 58 63 [];
    YP09.mkRegion (Some 9%nat) 96 104 0 0 [YP09.mkChunk 96 (CVal 8 (SOff 19 80))];
    YP09.mkRegion (Some 19%nat) 80 84 80 84 [] ].
Definition ss_gb0 : sstate := mkSS GPS_gbhd sr_atoms gb_rs0 None (mkFacts [] [] []).

(* The two 144-byte arrays of the frame keep their length through the set loop. *)
Lemma gb_set_len : forall cs T ws st,
  length ws = 144%nat -> length st = 144%nat ->
  length (snd (fst (fold_left set_step cs (T, ws, st)))) = 144%nat /\
  length (snd (fold_left set_step cs (T, ws, st))) = 144%nat.
Proof.
  induction cs as [|x cs IH]; intros T ws st Hws Hst; [cbn; auto|].
  destruct x as [[c q] v]. cbn [fold_left set_step].
  destruct ((c <? 48) && legalb q v)%bool eqn:Hg; [|apply IH; assumption].
  apply andb_prop in Hg as [Hc Hq]. apply Z.ltb_lt in Hc.
  assert (Hq2 : q <= 2).
  { unfold legalb in Hq. apply orb_prop in Hq as [Hq | Hq]; apply andb_prop in Hq as [Hq _];
    [apply Z.ltb_lt in Hq; lia | apply Z.eqb_eq in Hq; lia]. }
  apply IH; unfold ws_put; rewrite Mem.upd_bytes_length; (cbn [length]; lia).
Qed.

Lemma gb_ws_len : forall pl, length (ws_end pl) = 144%nat /\ length (st_end pl) = 144%nat.
Proof.
  intros pl. unfold ws_end, st_end, tables_end, tables_at, after_sets.
  apply gb_set_len; unfold Z144; apply repeat_length.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Lemma gb_ms_eta : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> ms_svc_pending ms = None -> ms_resv ms = None ->
  ms_rom ms = seg_rom SEGS ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (seg_rom SEGS).
Proof. intros [] H1 H2 H3 H4 H5; cbn in *; subst; reflexivity. Qed.
(* A one-byte chunk of a literal gives that byte of the state's memory. *)
Lemma gb_cv1 : forall (E' : env) (H : word -> bool) (mem : word -> option byte) base off v,
  YP09.chunk_ok SEGS E' (mrestrict H mem) base (YP09.mkChunk off (CVal 1 (SLit v))) -> 0 <= v < 256 ->
  aview SEGS H mem (base + off) = Some v.
Proof.
  intros E' H mem base off v Hc Hv.
  destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (b & Hb & Hm).
  cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm.
  unfold aview. rewrite Hm. injection Hb as <-. cbn [option_map].
  f_equal. unfold YP09.byte_of_word. cbn [sv_denot].
  rewrite Z.mul_0_r, Z.shiftr_0_r, unsigned_lit_small by lia. apply bv8_small. exact Hv.
Qed.

(* The same for a one-byte chunk whose value is any expression. *)
Lemma gb_cv1u : forall (E' : env) (H : word -> bool) (mem : word -> option byte) base off (e : sv) v,
  YP09.chunk_ok SEGS E' (mrestrict H mem) base (YP09.mkChunk off (CVal 1 e)) ->
  U E' e = v -> 0 <= v < 256 -> aview SEGS H mem (base + off) = Some v.
Proof.
  intros E' H mem base off e v Hc Hu Hv.
  destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (b & Hb & Hm).
  cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm.
  unfold aview. rewrite Hm. injection Hb as <-. cbn [option_map].
  f_equal. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
  change (bv_unsigned (sv_denot E' e)) with (U E' e). rewrite Hu. apply bv8_small. exact Hv.
Qed.


Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable GLOBS : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* The runtime and the callee, as GSW_RT and CtrlIdentityPollBlock.v give them. *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp).
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HGM : globs_marked SEGS B GLOBS.
Hypothesis TIPB : tctrl_identity_poll_block_spec B GLOBS.
(* The two read-only tables of the image this segment reads: GRANT_GROUPB (object 19,
   204 bytes, the six identity poll rows, which the callee copies) and POLL (object 6,
   18 bytes, the address and size of each one). *)
Hypothesis HGB_in : In (VAL (A_OBJ 19), 204) GLOBS.
Hypothesis HGB_lo : IMG_LO + 64 <= VAL (A_OBJ 19).
Hypothesis HGB_hi : VAL (A_OBJ 19) + 204 + 64 <= IMG_HI.
Hypothesis HGB : forall (H : word -> bool) (mem : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 19)) GBallz.
Hypothesis HPOLL_in : In (VAL (A_OBJ 6), 18) GLOBS.
Hypothesis HPOLL_lo : IMG_LO + 64 <= VAL (A_OBJ 6).
Hypothesis HPOLL_hi : VAL (A_OBJ 6) + 18 + 64 <= IMG_HI.
Hypothesis HPOLL : forall (H : word -> bool) (mem : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 6)) POLLz.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

Section t.
Variables (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (t s : Z) (i : nat).
Hypothesis HB : ge_base B MT cx.
Hypothesis HJ : ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : YG01.frames S3 = [(GE_CID, fp)].
Hypothesis HBODY : ge_body cx fp GPS_gbhd W3 ms3 GSH_a.
Hypothesis HBLK : gsw_blk B cx fp ly3 S3 W3 ms3 t s.
Hypothesis HROWS : gsw_rows cx W3 ms3 t s.
Hypothesis Hi : (i <= 5)%nat.
Hypothesis R18 : getr (ms_regs ms3) 18 = w64 (Z.of_nat i).
Hypothesis R27 : getr (ms_regs ms3) 27 = w64 (s + 190 + 34 * Z.of_nat i).
Hypothesis R26 : getr (ms_regs ms3) 26 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat i).
Hypothesis R21 : getr (ms_regs ms3) 21 = w64 (6 - Z.of_nat i).
Hypothesis R19 : getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_POLL).
Hypothesis R24 : getr (ms_regs ms3) 24 = w64 17.
Hypothesis R25 : getr (ms_regs ms3) 25 = w64 5.
Hypothesis R23 : getr (ms_regs ms3) 23 = w64 (-8).
Hypothesis R22 : getr (ms_regs ms3) 22 = w64 (gSH cx fp).
Hypothesis Hk2 : k <= 2.
Hypothesis Hacc : acc <= GE_A2 MT - mo_free MT.
(* The two ways out of a turn: round again at i + 1, or leave for the free of the sweep. *)
Hypothesis HLOOP : forall (ms' : machine_state) (md' : Model),
  (S i <= 5)%nat ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms') md' k ->
  ge_body cx fp GPS_gbhd W3 ms' GSH_a ->
  gsw_blk B cx fp ly3 S3 W3 ms' t s -> gsw_rows cx W3 ms' t s ->
  getr (ms_regs ms') 18 = w64 (Z.of_nat (S i)) ->
  getr (ms_regs ms') 27 = w64 (s + 190 + 34 * Z.of_nat (S i)) ->
  getr (ms_regs ms') 26 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat (S i)) ->
  getr (ms_regs ms') 21 = w64 (6 - Z.of_nat (S i)) ->
  getr (ms_regs ms') 19 = w64 (gF cx fp + GO_POLL) ->
  getr (ms_regs ms') 24 = w64 17 -> getr (ms_regs ms') 25 = w64 5 ->
  getr (ms_regs ms') 23 = w64 (-8) -> getr (ms_regs ms') 22 = w64 (gSH cx fp) ->
  SRr SEGS W3 (mkCfg ms' md') (ge_post B MT cx).
Hypothesis HEXIT : forall (ms' : machine_state) (md' : Model),
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms') md' k ->
  ge_body cx fp GPS_free1 W3 ms' GSH_a ->
  gsw_blk B cx fp ly3 S3 W3 ms' t s ->
  getr (ms_regs ms') 22 = w64 (gSH cx fp) ->
  SRr SEGS W3 (mkCfg ms' md') (ge_post B MT cx).

Lemma gb_frame_eq : forall c p, frame_addr ly3 c p = frame_addr (c_ly cx) c p.
Proof.
  intros c p. pose proof HJ as (_ & HLY & _). destruct HLY as (_ & _ & _ & _ & _ & HF & _).
  unfold frame_addr. rewrite HF. reflexivity.
Qed.

(* The frame, its shadow, the machine stack and the realigned stack pointer, as numbers. *)
Lemma gb_nums :
  gF cx fp mod 32 = 0 /\ 4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\ in_app (gF cx fp) 1024 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\ 8 * (gF cx fp / 8) = gF cx fp /\
  alloc_ceiling + GE_STK <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\ spZ (c_regs cx) mod 16 = 0 /\
  c_sp1 cx mod 32 = 0 /\ spZ (c_regs cx) - 304 <= c_sp1 cx <= spZ (c_regs cx) - 288 /\
  c_sp1 cx mod 16 = 0.
Proof.
  pose proof HJ as (HAR & _).
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1d & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR Hfin) as (HFal & HFia & _ & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ GE_CID fp HAR Hfin) as (HF4096 & HFceil & _).
  rewrite gb_frame_eq in HFal, HFia, HF4096, HFceil. fold (gF cx fp) in HFal, HFia, HF4096, HFceil.
  change (fs_frame_bytes GE_CID) with 1024 in HFia, HFceil.
  pose proof (Z.div_mod (gF cx fp) 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (gF cx fp) 8 ltac:(lia)) as M8.
  destruct (sp1_facts (spZ (c_regs cx) + -288) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
    as (Hsp1r & Hsp1al & Hsp1al16).
  rewrite <- Hsp1d in Hsp1r, Hsp1al.
  split; [exact HFal|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFia|].
  split; [unfold gSH, shadow_of_addr; reflexivity|]. split; [lia|].
  split; [unfold GE_STK in *; lia|]. split; [lia|]. split; [exact Hal16|]. split; [exact Hsp1al|].
  split; [lia|]. rewrite <- Hsp1d in Hsp1al16. exact Hsp1al16.
Qed.

(* ---- the environment of the turn: the registers at the head, and the image ---- *)
Definition gb_E : env := Eimg (Ereg (ms_regs ms3) []).

Lemma gb_EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew gb_E n = getr (ms_regs ms3) r.
Proof. intros nn r Hnn. apply ew_Eimg_Ereg_nat. exact Hnn. Qed.

Lemma gb_B22 : base_val gb_E (Some 22%nat) = gSH cx fp.
Proof.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & _).
  pose proof asan_consts as (C1 & _).
  cbn [base_val]. rewrite (gb_EE 22%nat 22%bv eq_refl), R22. apply unsigned_lit_small.
  pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (gF cx fp) 8 ltac:(lia)).
  rewrite ESH. unfold SHADOW_OFF. lia.
Qed.

Lemma gb_B9 : base_val gb_E (Some 9%nat) = c_sp1 cx.
Proof.
  pose proof gb_nums as (_ & _ & _ & _ & _ & _ & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & (_ & _ & Q9 & _) & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK in Hsp0lo.
  cbn [base_val]. rewrite (gb_EE 9%nat 9%bv eq_refl), Q9. apply unsigned_lit_small. lia.
Qed.

Lemma gb_B19 : base_val gb_E (Some 19%nat) = gF cx fp + GO_POLL.
Proof.
  pose proof gb_nums as (_ & HF4096 & HFceil & _). pose proof asan_consts as (C1 & _).
  cbn [base_val]. rewrite (gb_EE 19%nat 19%bv eq_refl), R19. apply unsigned_lit_small. unfold GO_POLL. lia.
Qed.

(* The image's read-only bytes are the same in every state this walk reaches. *)
Lemma gb_rod : forall (mem' : word -> option byte) md' k',
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem' md' k' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem').
Proof.
  intros mem' md' k' HJ' a Hro Ho He.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HROD & _).
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a).
  - exact (HROD a Hro Ho He).
  - destruct Hro as [(sg & Hs & _ & Hr) | Hgot]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hgot)].
  - exact Ho.
  - exact He.
  - apply fp_spares_closed. intros (r & [] & _).
Qed.

(* Every byte the turn writes is the walk's own: the frame's shadow window of `poll`
   and the four bytes of the compound literal, both inside the frame it owns. *)
Lemma gb_awr : forall (E' : env) (rs : YP09.smem),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 22 = ew gb_E 22 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  awr_ok E' rs GE_STK (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(GE_CID, fp)].
Proof.
  intros E' rs H9 H19 H22 Hsk a Hin.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & _).
  pose proof gb_B22 as B22. pose proof gb_B19 as B19.
  apply (in_wrange_skeleton E' rs gb_rs0 a Hsk) in Hin.
  unfold gb_rs0 in Hin. destruct Hin as (r & Hr & Ha).
  cbn [In] in Hr. cbn [base_val] in B22, B19.
  right; right; right. exists GE_CID, fp. split; [left; reflexivity|].
  rewrite gb_frame_eq. fold (gF cx fp). change (fs_frame_bytes GE_CID) with 1024.
  destruct Hr as [<- | [<- | [<- | []]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - right. rewrite H22, B22, ESH in Ha. unfold in_zr, shadow_addr. cbn [fst snd].
    change (1024 / 8) with 128. lia.
  - exfalso. lia.
  - left. rewrite H19, B19 in Ha. unfold in_zr. cbn [fst snd]. unfold GO_POLL in Ha. lia.
Qed.

(* The frame, its shadow bytes and the machine-stack window lie apart. *)
Lemma gb_sep :
  (gF cx fp + 1024 <= gSH cx fp \/ gSH cx fp + 128 <= gF cx fp) /\
  gSH cx fp + 128 <= c_sp1 cx - 8192 /\ gF cx fp + 1024 <= c_sp1 cx - 8192 /\ 0 <= gSH cx fp.
Proof.
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & Hsp0lo & Hsp0hi & Hsp0al & Hsp1al & Hsp1 & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK in Hsp0lo.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
  destruct HFia as (_ & [HA | (HB1 & HB2)]).
  - split; [left; rewrite ESH; unfold SHADOW_OFF; lia|].
    split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [lia|]. rewrite ESH; unfold SHADOW_OFF; lia.
  - split; [right; rewrite ESH; unfold SHADOW_OFF; lia|].
    split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [lia|]. rewrite ESH; unfold SHADOW_OFF; lia.
Qed.

Lemma gb_sh_nf : forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> ~ (gF cx fp <= a < gF cx fp + 1024).
Proof. intros a Ha. pose proof gb_sep as (HSEP & _). destruct HSEP; lia. Qed.

(* The three regions of the turn's state survive a call that keeps their bytes. *)
Lemma gb_kept : forall (E' : env) (m m' : word -> option byte) cs1 cs2 cs3,
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 22 = ew gb_E 22 ->
  (forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, c_sp1 cx + 96 <= a < c_sp1 cx + 104 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> apresent (w_H W3) m' a) ->
  (forall a, gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4 -> apresent (w_H W3) m' a) ->
  Forall (region_kept SEGS E' (mrestrict (w_H W3) m) (mrestrict (w_H W3) m'))
    [YP09.mkRegion (Some 22%nat) 58 63 58 63 cs1;
     YP09.mkRegion (Some 9%nat) 96 104 0 0 cs2;
     YP09.mkRegion (Some 19%nat) 80 84 80 84 cs3].
Proof.
  intros E' m m' cs1 cs2 cs3 H9 H19 H22 K22 K9 K19 P22 P19.
  pose proof gb_B22 as B22. pose proof gb_B9 as B9. pose proof gb_B19 as B19.
  cbn [base_val] in B22, B9, B19.
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?H9, ?H19, ?H22, ?B22, ?B9, ?B19; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply K22. exact Ha.
  - intros _. apply (apresent_writable SEGS). apply P22. exact Ha.
  - apply (mbyte_of_aview SEGS). apply K9. exact Ha.
  - lia.
  - apply (mbyte_of_aview SEGS). apply K19. unfold GO_LIT, GO_POLL in *. lia.
  - intros _. apply (apresent_writable SEGS). apply P19. unfold GO_LIT, GO_POLL in *. lia.
Qed.

(* The five shadow bytes the turn writes before the call: `poll` is usable. *)
Definition gb_sh5 (m : word -> option byte) : Prop :=
  aview SEGS (w_H W3) m (gSH cx fp + 58) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 59) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 60) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 61) = Some 0 /\
  aview SEGS (w_H W3) m (gSH cx fp + 62) = Some 2.

Lemma gb_sh5_tr : forall (m m' : word -> option byte),
  gb_sh5 m -> (forall a, gSH cx fp + 58 <= a < gSH cx fp + 63 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  gb_sh5 m'.
Proof.
  intros m m' (H58 & H59 & H60 & H61 & H62) HK. unfold gb_sh5.
  split; [rewrite HK by lia; exact H58|]. split; [rewrite HK by lia; exact H59|].
  split; [rewrite HK by lia; exact H60|]. split; [rewrite HK by lia; exact H61|].
  rewrite HK by lia. exact H62.
Qed.

(* Those five bytes say the 34 bytes of `poll` are usable. *)
Lemma gb_ra_of_sh5 : forall (m : word -> option byte),
  gb_sh5 m -> range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (gF cx fp + GO_POLL) 34.
Proof.
  intros m (C58 & C59 & C60 & C61 & C62).
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & _).
  assert (HD1 : (gF cx fp + 464) / 8 = gF cx fp / 8 + 58).
  { rewrite <- E8 at 1. replace (8 * (gF cx fp / 8) + 464) with ((gF cx fp / 8) * 8 + 464) by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  assert (HD2 : (gF cx fp + 464 + 32) / 8 = gF cx fp / 8 + 62).
  { rewrite <- E8 at 1. replace (8 * (gF cx fp / 8) + 464 + 32) with ((gF cx fp / 8) * 8 + 496) by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  assert (HM1 : (gF cx fp + 464) mod 8 = 0).
  { rewrite <- E8. replace (8 * (gF cx fp / 8) + 464) with ((gF cx fp / 8 + 58) * 8) by lia. apply Z_mod_mult. }
  assert (HM2 : (gF cx fp + 464 + 32) mod 8 = 0).
  { rewrite <- E8. replace (8 * (gF cx fp / 8) + 464 + 32) with ((gF cx fp / 8 + 62) * 8) by lia. apply Z_mod_mult. }
  unfold GO_POLL. replace 34 with (32 + 2) by lia. apply range_addressable_app; [lia| |].
  - apply zero_shadow_range; [exact HM1 | reflexivity |].
    intros j Hj. change (32 / 8) with 4 in Hj. unfold shadow_of_addr. rewrite HD1.
    assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj4 as [-> | [-> | [-> | ->]]].
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 0) with (gSH cx fp + 58) by (rewrite ESH; lia). exact C58.
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 1) with (gSH cx fp + 59) by (rewrite ESH; lia). exact C59.
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 2) with (gSH cx fp + 60) by (rewrite ESH; lia). exact C60.
    + replace (SHADOW_OFF + (gF cx fp / 8 + 58) + 3) with (gSH cx fp + 61) by (rewrite ESH; lia). exact C61.
  - apply (range_addressable_partial _ SHADOW_OFF (gF cx fp + 464 + 32) 2); [|exact HM2 | lia].
    unfold shadow_of_addr. rewrite HD2.
    replace (SHADOW_OFF + (gF cx fp / 8 + 62)) with (gSH cx fp + 62) by (rewrite ESH; lia). exact C62.
Qed.

Lemma gb_garr8_tr : forall (m m' : word -> option byte) b l,
  garr8 SEGS (mrestrict (w_H W3) m) b l ->
  (forall a, b <= a < b + Z.of_nat (length l) -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  garr8 SEGS (mrestrict (w_H W3) m') b l.
Proof.
  intros m m' b l Hg HK. apply (garr8_frame SEGS (mrestrict (w_H W3) m)); [exact Hg|].
  intros a Ha. apply (mbyte_of_aview SEGS). apply HK. exact Ha.
Qed.

(* The sweep the box built: its block, its length, and its row 5 + i. *)
Lemma gb_rows_ok : ok (c_pl cx) = true /\ 1 <= sw_in (c_pl cx) <= 40 /\ 11 <= sw_rows (c_pl cx).
Proof.
  pose proof HROWS as (Hok & Hwant & _).
  pose proof Hok as Hf. unfold ok, fits in Hf.
  apply andb_prop in Hf as [Hf Hbw]. apply andb_prop in Hf as [Hf Hb0].
  apply andb_prop in Hf as [Hf1 Hf40]. apply Z.leb_le in Hf1, Hf40, Hb0, Hbw.
  unfold sw_want in *. unfold sw_in in *. split; [exact Hok|]. split; [lia | lia].
Qed.

Lemma gb_len_concat34 : forall (L : list (list byte)),
  Forall (fun r => length r = 34%nat) L -> length (concat L) = (34 * length L)%nat.
Proof.
  induction L as [|r L IH]; intros HL; [reflexivity|].
  inversion HL as [|r0 L0 Hr HL']; subst r0 L0.
  cbn [concat length]. rewrite length_app, Hr, (IH HL'). lia.
Qed.

Lemma gb_sweep_len : Z.of_nat (length (sw_bytes (c_pl cx) t)) = 34 * (8 + 3 * sw_in (c_pl cx)).
Proof.
  pose proof gb_rows_ok as (_ & Hin & _).
  unfold sw_bytes. rewrite SWEEP_rows, gb_len_concat34 by (apply Forall_rowok_len, sweep_rows_ok).
  rewrite Nat2Z.inj_mul,
    (length_sweep_rows (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t) ltac:(lia)).
  lia.
Qed.


Lemma gb_rowlen : Z.of_nat (length (sw_bytes (c_pl cx) t)) <= sw_mbytes (c_pl cx).
Proof.
  pose proof gb_sweep_len as HL. pose proof HROWS as (_ & Hwant & _).
  unfold sw_mbytes. unfold sw_want in Hwant. destruct (Z.ltb_spec 0 (sw_rows (c_pl cx))); lia.
Qed.
Lemma gb_blk : In (s, sw_mbytes (c_pl cx)) (ablocks B ly3 S3) /\ 0 < s /\ 374 <= sw_mbytes (c_pl cx).
Proof.
  pose proof HBLK as (_ & Hsin & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & Hs0 & _).
  pose proof gb_rows_ok as (_ & _ & Hr11).
  split; [exact Hsin|]. split; [exact Hs0|]. unfold sw_mbytes.
  destruct (Z.ltb_spec 0 (sw_rows (c_pl cx))); lia.
Qed.

(* The call left `poll` holding GBz i; row 5 + i of the sweep holds the same bytes. *)
Lemma gb_row_eq : forall (m : word -> option byte) j,
  garr8 SEGS (mrestrict (w_H W3) m) (gF cx fp + GO_POLL) (GBz (Z.of_nat i)) ->
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  0 <= j < 34 ->
  aview SEGS (w_H W3) m (gF cx fp + GO_POLL + j) = aview SEGS (w_H W3) m (s + 170 + 34 * Z.of_nat i + j).
Proof.
  intros m j HP HR Hj.
  pose proof gb_rows_ok as (Hok & Hin1 & _). pose proof gb_sweep_len as HL.
  destruct (garr8_nthZ SEGS _ _ _ j HP ltac:(lia) ltac:(rewrite ipb_gbz_len; lia)) as (Hv1 & Hr1).
  destruct (garr8_nthZ SEGS _ _ _ (34 * (5 + Z.of_nat i) + j) HR ltac:(lia)
              ltac:(rewrite length_map; lia)) as (Hv2 & Hr2).
  assert (HE : nth (Z.to_nat (34 * (5 + Z.of_nat i) + j))
                 (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) 0
               = nth (Z.to_nat j) (GBz (Z.of_nat i)) 0).
  { replace (Z.to_nat (34 * (5 + Z.of_nat i) + j)) with (34 * (5 + i) + Z.to_nat j)%nat by lia.
    apply gb_row_bytes; [exact Hok | exact Hi | lia]. }
  rewrite HE in Hv2, Hr2.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv1 Hr1).
  replace (s + 170 + 34 * Z.of_nat i + j) with (s + (34 * (5 + Z.of_nat i) + j)) by lia.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv2 Hr2). reflexivity.
Qed.

(* Row 5 + i at offset 16 holds the four bytes of the compound literal. *)
Lemma gb_lit_eq : forall (m : word -> option byte) j,
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  (forall j', 0 <= j' < 4 -> aview SEGS (w_H W3) m (gF cx fp + GO_LIT + j') = Some (nth (Z.to_nat j') LITz 0)) ->
  0 <= j < 4 ->
  aview SEGS (w_H W3) m (s + 170 + 34 * Z.of_nat i + 16 + j) = aview SEGS (w_H W3) m (gF cx fp + GO_LIT + j).
Proof.
  intros m j HR HL4 Hj.
  pose proof gb_rows_ok as (Hok & Hin1 & _). pose proof gb_sweep_len as HL.
  destruct (garr8_nthZ SEGS _ _ _ (34 * (5 + Z.of_nat i) + 16 + j) HR ltac:(lia)
              ltac:(rewrite length_map; lia)) as (Hv2 & Hr2).
  assert (HE : nth (Z.to_nat (34 * (5 + Z.of_nat i) + 16 + j))
                 (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) 0
               = nth (Z.to_nat j) LITz 0).
  { replace (Z.to_nat (34 * (5 + Z.of_nat i) + 16 + j)) with (34 * (5 + i) + (16 + Z.to_nat j))%nat by lia.
    rewrite gb_row_bytes by (first [exact Hok | exact Hi | lia]).
    replace (16 + Z.to_nat j)%nat with (16 + Z.to_nat j)%nat by reflexivity.
    apply gb_lit_bytes; [exact Hi | lia]. }
  rewrite HE in Hv2, Hr2.
  replace (s + 170 + 34 * Z.of_nat i + 16 + j) with (s + (34 * (5 + Z.of_nat i) + 16 + j)) by lia.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv2 Hr2), (HL4 j Hj). reflexivity.
Qed.

(* Row 5 + i at offset 20 holds the three bytes POLL[i] of the image. *)
Lemma gb_pollt_eq : forall (m : word -> option byte) j,
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  garr8 SEGS (mrestrict (w_H W3) m) (VAL (A_OBJ 6)) POLLz ->
  0 <= j < 3 ->
  aview SEGS (w_H W3) m (s + 170 + 34 * Z.of_nat i + 20 + j)
  = aview SEGS (w_H W3) m (VAL (A_OBJ 6) + 3 * Z.of_nat i + j).
Proof.
  intros m j HR HP Hj.
  pose proof gb_rows_ok as (Hok & Hin1 & _). pose proof gb_sweep_len as HL.
  destruct (garr8_nthZ SEGS _ _ _ (34 * (5 + Z.of_nat i) + 20 + j) HR ltac:(lia)
              ltac:(rewrite length_map; lia)) as (Hv2 & Hr2).
  destruct (garr8_nthZ SEGS _ _ _ (3 * Z.of_nat i + j) HP ltac:(lia) ltac:(cbn [length POLLz]; lia))
    as (Hv3 & Hr3).
  assert (HE : nth (Z.to_nat (34 * (5 + Z.of_nat i) + 20 + j))
                 (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) 0
               = nth (Z.to_nat (3 * Z.of_nat i + j)) POLLz 0).
  { replace (Z.to_nat (34 * (5 + Z.of_nat i) + 20 + j)) with (34 * (5 + i) + (20 + Z.to_nat j))%nat by lia.
    rewrite gb_row_bytes by (first [exact Hok | exact Hi | lia]).
    replace (Z.to_nat (3 * Z.of_nat i + j)) with (3 * i + Z.to_nat j)%nat by lia.
    symmetry. apply gb_poll_bytes; [exact Hi | lia]. }
  rewrite HE in Hv2, Hr2.
  replace (s + 170 + 34 * Z.of_nat i + 20 + j) with (s + (34 * (5 + Z.of_nat i) + 20 + j)) by lia.
  replace (VAL (A_OBJ 6) + 3 * Z.of_nat i + j) with (VAL (A_OBJ 6) + (3 * Z.of_nat i + j)) by lia.
  rewrite (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv2 Hr2),
          (aview_of_val_mem1 SEGS (w_H W3) m _ _ Hv3 Hr3). reflexivity.
Qed.

Lemma gb_sh_nf2 : forall a, gSH cx fp <= a < gSH cx fp + 128 -> ~ (gF cx fp <= a < gF cx fp + 1024).
Proof.
  intros a Ha. pose proof gb_nums as (_ & HF4096 & HFceil & HFia & ESH & E8 & _).
  pose proof asan_consts as (C1 & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
  destruct HFia as (_ & [HA | (HB1 & HB2)]); rewrite ESH in Ha; unfold SHADOW_OFF in Ha; lia.
Qed.

(* What the whole turn leaves alone: all but its stack windows, `poll`, the five shadow
   bytes of `poll` and the four bytes of the compound literal. *)
Definition gb_tkeep (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 ->
    ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
    ~ (gF cx fp + GO_POLL <= a < gF cx fp + GO_POLL + 34) ->
    ~ (gSH cx fp + 58 <= a < gSH cx fp + 63) ->
    ~ (gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4) ->
    aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma gb_tkeep_refl : forall m, gb_tkeep m m.
Proof. intros m a _ _ _ _ _. reflexivity. Qed.

Lemma gb_tkeep_trans : forall m1 m2 m3, gb_tkeep m1 m2 -> gb_tkeep m2 m3 -> gb_tkeep m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha Aa Bb Cc Dd. rewrite (H2 a Ha Aa Bb Cc Dd). exact (H1 a Ha Aa Bb Cc Dd). Qed.

(* The frame's shadow byte of the compound literal: in scope from the first slot. *)
Lemma gb_sh68 : forall m, gb_tkeep (ms_mem ms3) m -> aview SEGS (w_H W3) m (gSH cx fp + 68) = Some 4.
Proof.
  intros m HTK.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK in Hsp0lo.
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & _ & Hgsh & _).
  assert (H68 : aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + 68) = Some 4).
  { pose proof (Hgsh 68%nat ltac:(vm_compute; lia)) as H. cbn [Z.of_nat] in H.
    replace (nth 68 GSH_a 0) with 4 in H by (vm_compute; reflexivity). exact H. }
  rewrite HTK.
  - exact H68.
  - lia.
  - lia.
  - intros HC. apply (gb_sh_nf2 (gSH cx fp + 68) ltac:(lia)). unfold GO_POLL in HC. lia.
  - lia.
  - intros HC. apply (gb_sh_nf2 (gSH cx fp + 68) ltac:(lia)). unfold GO_LIT in HC. lia.
Qed.

Lemma gb_ra_lit : forall (m : word -> option byte),
  aview SEGS (w_H W3) m (gSH cx fp + 68) = Some 4 ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (gF cx fp + GO_LIT) 4.
Proof.
  intros m H68. pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & _).
  assert (HD : (gF cx fp + 544) / 8 = gF cx fp / 8 + 68).
  { rewrite <- E8 at 1. replace (8 * (gF cx fp / 8) + 544) with ((gF cx fp / 8) * 8 + 544) by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  assert (HM : (gF cx fp + 544) mod 8 = 0).
  { rewrite <- E8. replace (8 * (gF cx fp / 8) + 544) with ((gF cx fp / 8 + 68) * 8) by lia. apply Z_mod_mult. }
  unfold GO_LIT. apply (range_addressable_partial _ SHADOW_OFF (gF cx fp + 544) 4); [|exact HM | lia].
  unfold shadow_of_addr. rewrite HD.
  replace (SHADOW_OFF + (gF cx fp / 8 + 68)) with (gSH cx fp + 68) by (rewrite ESH; lia). exact H68.
Qed.

(* The four bytes of the compound literal, read back from the walk's own state. *)
Lemma gb_lit4_of_state : forall (E' : env) (ss : sstate) (msx : machine_state),
  st_ok SEGS E' ss (restrict (w_H W3) msx) ->
  ew E' 19 = ew gb_E 19 -> ew E' 24 = ew gb_E 24 -> ew E' 25 = ew gb_E 25 ->
  nth_error (ss_mem ss) 2 = Some (YP09.mkRegion (Some 19%nat) 80 84 80 84
    [YP09.mkChunk 83 (CVal 1 (SLit 0)); YP09.mkChunk 82 (CVal 1 (SOff 25 0));
     YP09.mkChunk 81 (CVal 1 (SOff 24 0)); YP09.mkChunk 80 (CVal 1 (SLit 18))]) ->
  forall j, 0 <= j < 4 ->
  aview SEGS (w_H W3) (ms_mem msx) (gF cx fp + GO_LIT + j) = Some (nth (Z.to_nat j) LITz 0).
Proof.
  intros E' ss msx HS H19 H24 H25 Hnth j Hj.
  pose proof gb_B19 as B19. cbn [base_val] in B19.
  destruct (st_ok_region_nth E' ss _ 2%nat _ HS Hnth) as (_ & _ & _ & HC).
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite H19, B19 in HC.
  inversion HC as [|?? C83 HC1]; subst. inversion HC1 as [|?? C82 HC2]; subst.
  inversion HC2 as [|?? C81 HC3]; subst. inversion HC3 as [|?? C80 HC4]; subst.
  cbn [ms_mem restrict] in C80, C81, C82, C83.
  apply (gb_cv1u E' (w_H W3) (ms_mem msx) _ 83 (SLit 0) 0) in C83;
    [|rewrite U_SLit; reflexivity | lia].
  apply (gb_cv1u E' (w_H W3) (ms_mem msx) _ 82 (SOff 25 0) 5) in C82;
    [|rewrite U_SOff, H25, (gb_EE 25%nat 25%bv eq_refl), R25; reflexivity | lia].
  apply (gb_cv1u E' (w_H W3) (ms_mem msx) _ 81 (SOff 24 0) 17) in C81;
    [|rewrite U_SOff, H24, (gb_EE 24%nat 24%bv eq_refl), R24; reflexivity | lia].
  apply (gb_cv1u E' (w_H W3) (ms_mem msx) _ 80 (SLit 18) 18) in C80;
    [|rewrite U_SLit; reflexivity | lia].
  assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  unfold GO_LIT. destruct Hj4 as [-> | [-> | [-> | ->]]]; cbn [LITz nth Z.to_nat Pos.to_nat].
  - replace (gF cx fp + 544 + 0) with (gF cx fp + 464 + 80) by lia. exact C80.
  - replace (gF cx fp + 544 + 1) with (gF cx fp + 464 + 81) by lia. exact C81.
  - replace (gF cx fp + 544 + 2) with (gF cx fp + 464 + 82) by lia. exact C82.
  - replace (gF cx fp + 544 + 3) with (gF cx fp + 464 + 83) by lia. exact C83.
Qed.

(* The sweep block: where it lies, and that it lies apart from the frame. *)
Lemma gb_sbnd : 4096 <= s /\ s + req_size (sw_mbytes (c_pl cx)) <= alloc_ceiling /\
  in_app s (req_size (sw_mbytes (c_pl cx))) /\ sw_mbytes (c_pl cx) <= req_size (sw_mbytes (c_pl cx)) /\
  (s + req_size (sw_mbytes (c_pl cx)) <= gF cx fp \/ gF cx fp + 1024 <= s) /\
  (s + req_size (sw_mbytes (c_pl cx)) <= gSH cx fp \/ gSH cx fp + 128 <= s) /\
  s + req_size (sw_mbytes (c_pl cx)) <= c_sp1 cx - 8192.
Proof.
  pose proof (proj1 HJ) as HAR. pose proof gb_blk as (Hsin & Hs0 & Hsm).
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR Hsin)
    as (_ & Hs4096 & Hsceil & Hsapp & _ & _).
  pose proof (req_size_pos' (sw_mbytes (c_pl cx)) ltac:(lia)) as (_ & Hreq).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 s (sw_mbytes (c_pl cx)) GE_CID fp
                HAR Hsin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite gb_frame_eq in Hd. fold (gF cx fp) in Hd.
  change (fs_frame_bytes GE_CID) with 1024 in Hd.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK in Hsp0lo.
  split; [exact Hs4096|]. split; [exact Hsceil|]. split; [exact Hsapp|]. split; [exact Hreq|].
  split; [exact Hd|]. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hsapp.
  split; [rewrite ESH; unfold SHADOW_OFF; destruct Hsapp as (_ & [HA | (HB1 & HB2)]); lia | lia].
Qed.

(* What a call of this turn leaves alone: everything but its own stack window and `poll`. *)
Definition gb_keep (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
    ~ (gF cx fp + GO_POLL <= a < gF cx fp + GO_POLL + 34) ->
    aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma gb_tkeep_of_keep : forall m m', gb_keep m m' -> gb_tkeep m m'.
Proof. intros m m' HK a Ha Aa Bb _ _. exact (HK a Ha Aa Bb). Qed.

(* The two facts of the turn that must cross every call. *)
Definition gb_mem (m : word -> option byte) : Prop :=
  gb_sh5 m /\
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)).

Lemma gb_mem_tr : forall m m', gb_mem m -> gb_keep m m' -> gb_mem m'.
Proof.
  intros m m' (H5 & Hg) HK.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0).
  pose proof gb_sbnd as (Hs4096 & Hsceil & _ & Hreq & Hsep & Hsepsh & Hsstk).
  pose proof gb_rows_ok as (_ & Hin1 & Hr11). pose proof gb_sweep_len as HL.
  pose proof asan_consts as (C1 & _). unfold GE_STK in Hsp0lo.
  pose proof gb_blk as (_ & Hs0 & Hsm).
  assert (Hmb : 34 * (8 + 3 * sw_in (c_pl cx)) <= sw_mbytes (c_pl cx)).
  { pose proof HROWS as (_ & Hwant & _). unfold sw_mbytes. unfold sw_want in Hwant.
    destruct (Z.ltb_spec 0 (sw_rows (c_pl cx))); lia. }
  split.
  - apply (gb_sh5_tr m); [exact H5|]. intros a Ha. apply HK; [lia | lia|].
    intros HC. apply (gb_sh_nf a Ha). unfold GO_POLL in HC. lia.
  - apply (gb_garr8_tr m); [exact Hg|]. intros a Ha. rewrite length_map in Ha.
    apply HK; [lia | lia|]. unfold GO_POLL. lia.
Qed.

(* The five shadow bytes, read back from the walk's own symbolic state. *)
Lemma gb_sh5_of_state : forall (E' : env) (ss : sstate) (msx : machine_state),
  st_ok SEGS E' ss (restrict (w_H W3) msx) -> ew E' 22 = ew gb_E 22 ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 22%nat) 58 63 58 63
     [YP09.mkChunk 62 (CVal 1 (SLit 2)); YP09.mkChunk 61 (CVal 1 (SLit 0));
      YP09.mkChunk 60 (CVal 1 (SLit 0)); YP09.mkChunk 59 (CVal 1 (SLit 0));
      YP09.mkChunk 58 (CVal 1 (SLit 0))]) ->
  gb_sh5 (ms_mem msx).
Proof.
  intros E' ss msx HS H22 Hnth.
  pose proof gb_B22 as B22. cbn [base_val] in B22.
  destruct (st_ok_region_nth E' ss _ 0%nat _ HS Hnth) as (_ & _ & _ & HC).
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite H22, B22 in HC.
  inversion HC as [|?? C62 HC1]; subst. inversion HC1 as [|?? C61 HC2]; subst.
  inversion HC2 as [|?? C60 HC3]; subst. inversion HC3 as [|?? C59 HC4]; subst.
  inversion HC4 as [|?? C58 HC5]; subst.
  cbn [ms_mem restrict] in C58, C59, C60, C61, C62.
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 62 2) in C62; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 61 0) in C61; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 60 0) in C60; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 59 0) in C59; [|lia].
  apply (gb_cv1 E' (w_H W3) (ms_mem msx) (gSH cx fp) 58 0) in C58; [|lia].
  repeat split; assumption.
Qed.

(* The only bytes a run of this turn writes are those five and the four of the literal. *)
Lemma gb_wrange : forall (E' : env) (rs : YP09.smem),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 22 = ew gb_E 22 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  forall a, in_wrange E' rs a ->
    (gSH cx fp + 58 <= a < gSH cx fp + 63) \/ (gF cx fp + GO_LIT <= a < gF cx fp + GO_LIT + 4).
Proof.
  intros E' rs H9 H19 H22 Hsk a Hin.
  pose proof gb_B22 as B22. pose proof gb_B19 as B19. cbn [base_val] in B22, B19.
  apply (in_wrange_skeleton E' rs gb_rs0 a Hsk) in Hin.
  unfold gb_rs0 in Hin. destruct Hin as (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite H22, B22 in Ha. lia.
  - exfalso. lia.
  - right. rewrite H19, B19 in Ha. unfold GO_LIT, GO_POLL in *. lia.
Qed.

Lemma gb_tkeep_run : forall (E' : env) (rs : YP09.smem) (m m' : word -> option byte),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 22 = ew gb_E 22 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  frame_of E' rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  gb_tkeep m m'.
Proof.
  intros E' rs m m' H9 H19 H22 Hsk HFr a Ha Aa Bb Cc Dd.
  unfold aview. f_equal. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros Hw. rewrite unsigned_lit_small in Hw by lia.
  destruct (gb_wrange E' rs H9 H19 H22 Hsk a Hw) as [Hsh | Hlit]; [exact (Cc Hsh) | exact (Dd Hlit)].
Qed.

(* What the turn keeps, read on a block, on the frame and on the machine stack. *)
Lemma gb_blk_tkeep : forall (p n : Z) (m m' : word -> option byte),
  In (p, n) (ablocks B ly3 S3) -> gb_tkeep m m' ->
  forall a, p <= a < p + n -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
  intros p n m m' Hin HTK a Ha.
  pose proof (proj1 HJ) as HAR.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK in Hsp0lo.
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & Hn0).
  pose proof (req_size_pos' n ltac:(lia)) as (_ & Hreq).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 p n GE_CID fp HAR Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite gb_frame_eq in Hd. fold (gF cx fp) in Hd.
  change (fs_frame_bytes GE_CID) with 1024 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  apply HTK.
  - lia.
  - lia.
  - unfold GO_POLL. lia.
  - rewrite ESH. unfold SHADOW_OFF. destruct Hpapp as (_ & [HA | (HB1 & HB2)]); lia.
  - unfold GO_LIT. lia.
Qed.

Lemma gb_frm_tkeep : forall (o : Z) (m m' : word -> option byte),
  gb_tkeep m m' -> 0 <= o < 1024 ->
  ~ (GO_POLL <= o < GO_POLL + 34) -> ~ (GO_LIT <= o < GO_LIT + 4) ->
  aview SEGS (w_H W3) m' (gF cx fp + o) = aview SEGS (w_H W3) m (gF cx fp + o).
Proof.
  intros o m m' HTK Ho Hp Hl.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK in Hsp0lo.
  apply HTK.
  - lia.
  - lia.
  - unfold GO_POLL in *. lia.
  - intros HC. apply (gb_sh_nf2 (gF cx fp + o) ltac:(lia)). lia.
  - unfold GO_LIT in *. lia.
Qed.

Lemma gb_stk_tkeep : forall (a : Z) (m m' : word -> option byte),
  gb_tkeep m m' -> c_sp1 cx <= a < spZ (c_regs cx) ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
  intros a m m' HTK Ha.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK in Hsp0lo.
  apply HTK.
  - lia.
  - lia.
  - unfold GO_POLL. lia.
  - lia.
  - unfold GO_LIT. lia.
Qed.

Lemma gb_rdword_tr : forall (m m' : word -> option byte) a v,
  rdword (aview SEGS (w_H W3) m) a = Some v ->
  (forall x, a <= x < a + 8 -> aview SEGS (w_H W3) m' x = aview SEGS (w_H W3) m x) ->
  rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros m m' a v Hr HK. unfold rdword in *.
  rewrite (HK a ltac:(lia)), (HK (a+1) ltac:(lia)), (HK (a+2) ltac:(lia)), (HK (a+3) ltac:(lia)),
          (HK (a+4) ltac:(lia)), (HK (a+5) ltac:(lia)), (HK (a+6) ltac:(lia)), (HK (a+7) ltac:(lia)).
  exact Hr.
Qed.

(* `addiw` of 1 on a counter below six. *)
Lemma gb_addiw1 : forall z, 0 <= z <= 5 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 z)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (z + 1).
Proof.
  intros z Hz.
  assert (C : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* ---- the landing: the machine state at the next cut ---- *)
Lemma gb_land_body : forall (ms' : machine_state) (pc : Z),
  ms_pc_val ms' = Z_to_bv 64 (BASE + pc) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = w64 (c_sp1 cx) -> getr (ms_regs ms') 8 = w64 (spZ (c_regs cx)) ->
  getr (ms_regs ms') 9 = w64 (c_sp1 cx) ->
  getr (ms_regs ms') 3 = getr (c_regs cx) 3 -> getr (ms_regs ms') 4 = getr (c_regs cx) 4 ->
  gb_tkeep (ms_mem ms3) (ms_mem ms') ->
  (forall j, (58 <= j < 63)%nat ->
     aview SEGS (w_H W3) (ms_mem ms') (gSH cx fp + Z.of_nat j) = Some 248) ->
  ge_body cx fp pc W3 ms' GSH_a.
Proof.
  intros ms' pc Hpc Hrv Hsvc Hrom Hfr Hfc G2 G8 G9 G3 G4 HTK H248.
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSAVED0 & HSHAD0 & HFLAG0 & HLEN0 & HIN0).
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0). pose proof asan_consts as (C1 & _).
  unfold GE_STK in Hsp0lo.
  pose proof HB as (_ & _ & _ & Hpn & _).
  pose proof HBLK as (Ebl & _).
  split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsvc|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hfc|].
  split; [repeat split; assumption|].
  split.
  { destruct HSAVED0 as (Hra0 & Hsv0). split.
    - apply (gb_rdword_tr (ms_mem ms3)); [exact Hra0|].
      intros x Hx. apply gb_stk_tkeep; [exact HTK | lia].
    - intros j Hj. apply (gb_rdword_tr (ms_mem ms3)); [exact (Hsv0 j Hj)|].
      intros x Hx. apply gb_stk_tkeep; [exact HTK | lia]. }
  split.
  { intros j Hj. rewrite HLEN0 in Hj. unfold GE_NSH in Hj.
    destruct (Nat.lt_ge_cases j 58%nat) as [Hlo | Hge].
    - rewrite (HTK (gSH cx fp + Z.of_nat j));
        [ exact (HSHAD0 j ltac:(rewrite HLEN0; unfold GE_NSH; lia))
        | lia | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_POLL in HC; lia
        | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_LIT in HC; lia ].
    - destruct (Nat.lt_ge_cases j 63%nat) as [Hhi | Hge2].
      + rewrite (H248 j ltac:(lia)).
        assert (C : (j = 58 \/ j = 59 \/ j = 60 \/ j = 61 \/ j = 62)%nat) by lia.
        destruct C as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity.
      + rewrite (HTK (gSH cx fp + Z.of_nat j));
        [ exact (HSHAD0 j ltac:(rewrite HLEN0; unfold GE_NSH; lia))
        | lia | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_POLL in HC; lia
        | lia
        | intros HC; apply (gb_sh_nf2 (gSH cx fp + Z.of_nat j) ltac:(lia)); unfold GO_LIT in HC; lia ]. }
  split.
  { apply (gb_rdword_tr (ms_mem ms3)); [exact HFLAG0|].
    intros x Hx. replace x with (gF cx fp + (x - gF cx fp)) by lia.
    apply gb_frm_tkeep; [exact HTK | lia | unfold GO_POLL; lia | unfold GO_LIT; lia]. }
  split; [exact HLEN0|].
  apply (gb_garr8_tr (ms_mem ms3)); [exact HIN0|].
  intros a Ha. rewrite length_map in Ha.
  destruct Hpn as [(Hn0 & _) | (Hn0 & Hin)].
  - exfalso. unfold c_n in Hn0. lia.
  - apply (gb_blk_tkeep (c_p cx) (c_n cx)); [rewrite Ebl; apply in_or_app; left; exact Hin | exact HTK |].
    unfold c_n in *. lia.
Qed.

Lemma gb_land_blk : forall (ms' : machine_state),
  gb_tkeep (ms_mem ms3) (ms_mem ms') -> getr (ms_regs ms') 20 = w64 t ->
  gsw_blk B cx fp ly3 S3 W3 ms' t s.
Proof.
  intros ms' HTK G20.
  pose proof HBLK as (Ebl & Hsin & HTAB & HWAS & HSET & HREL & HI1 & HLATE & S88 & S120 & S96 & S64
                      & _ & Hn26 & Ht0 & Hs0 & HA).
  pose proof (gb_ws_len (c_pl cx)) as (Hwsl & Hstl).
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof asan_consts as (C1 & _). unfold GE_STK in Hsp0lo.
  assert (SLOT : forall off v, gslot cx W3 ms3 off v -> 0 <= off <= 184 -> gslot cx W3 ms' off v).
  { intros off v Hs' Hoff. unfold gslot in *. apply (gb_rdword_tr (ms_mem ms3)); [exact Hs'|].
    intros x Hx. apply gb_stk_tkeep; [exact HTK | lia]. }
  assert (FB : forall o v, gfb cx fp W3 ms3 o v -> 0 <= o < 1024 ->
                 ~ (GO_POLL <= o < GO_POLL + 34) -> ~ (GO_LIT <= o < GO_LIT + 4) -> gfb cx fp W3 ms' o v).
  { intros o v Hb Ho Hp Hl. unfold gfb in *. rewrite (gb_frm_tkeep o _ _ HTK Ho Hp Hl). exact Hb. }
  split; [exact Ebl|]. split; [exact Hsin|].
  split.
  { destruct HTAB as (Htin & Ht0' & HTlen & HTb). split; [exact Htin|]. split; [exact Ht0'|].
    split; [exact HTlen|]. intros ii H1 H2 H3 H4.
    rewrite (gb_blk_tkeep t 460 (ms_mem ms3) (ms_mem ms') Htin HTK (t + ii) ltac:(lia)).
    exact (HTb ii H1 H2 H3 H4). }
  split.
  { unfold gfarr in *. apply (gb_garr8_tr (ms_mem ms3)); [exact HWAS|].
    intros a Ha. rewrite length_map, Hwsl in Ha. replace a with (gF cx fp + (a - gF cx fp)) by lia.
    apply gb_frm_tkeep;
      [exact HTK | unfold GO_WAS in *; lia | unfold GO_WAS, GO_POLL in *; lia
       | unfold GO_WAS, GO_LIT in *; lia]. }
  split.
  { unfold gfarr in *. apply (gb_garr8_tr (ms_mem ms3)); [exact HSET|].
    intros a Ha. rewrite length_map, Hstl in Ha. replace a with (gF cx fp + (a - gF cx fp)) by lia.
    apply gb_frm_tkeep;
      [exact HTK | unfold GO_SET in *; lia | unfold GO_SET, GO_POLL in *; lia
       | unfold GO_SET, GO_LIT in *; lia]. }
  split; [exact HREL|]. split; [exact HI1|].
  split.
  { unfold gslots_late, gslots_mid in HLATE |- *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; (apply SLOT; [assumption | lia]). }
  split; [apply SLOT; [exact S88 | lia]|].
  split; [apply SLOT; [exact S120 | lia]|].
  split; [apply SLOT; [exact S96 | lia]|].
  split; [apply SLOT; [exact S64 | lia]|].
  split; [exact G20|]. split; [exact Hn26|]. split; [exact Ht0|]. split; [exact Hs0|].
  destruct (ok (c_pl cx)); destruct HA as (HA1 & HA2);
    split; apply FB; try assumption; unfold GO_A, GO_POLL, GO_LIT; lia.
Qed.

Lemma gb_land_rows : forall (ms' : machine_state),
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) s
    (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  gsw_rows cx W3 ms' t s.
Proof.
  intros ms' Hg. pose proof HROWS as (Hok & Hwant & _).
  split; [exact Hok|]. split; [exact Hwant | exact Hg].
Qed.

(* The five shadow bytes of `poll`, back at 0xf8, read from the walk's own state. *)
Lemma gb_cv1m : forall (E' : env) (H : word -> bool) (mem : word -> option byte) base off (e : sv) v,
  YP09.chunk_ok SEGS E' (mrestrict H mem) base (YP09.mkChunk off (CVal 1 e)) ->
  U E' e mod 256 = v -> 0 <= v < 256 -> aview SEGS H mem (base + off) = Some v.
Proof.
  intros E' H mem base off e v Hc Hu Hv.
  destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (b & Hb & Hm).
  cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm.
  unfold aview. rewrite Hm. injection Hb as <-. cbn [option_map].
  f_equal. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
  change (bv_unsigned (sv_denot E' e)) with (U E' e).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hu.
Qed.

Lemma gb_sh5f_of_state : forall (E' : env) (ss : sstate) (msx : machine_state),
  st_ok_pi SEGS VAL E' ss (restrict (w_H W3) msx) ->
  ew E' 22 = ew gb_E 22 -> ew E' 23 = ew gb_E 23 ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 22%nat) 58 63 58 63
     [YP09.mkChunk 62 (CVal 1 (SOff 23 0)); YP09.mkChunk 61 (CVal 1 (SOff 23 0));
      YP09.mkChunk 60 (CVal 1 (SOff 23 0)); YP09.mkChunk 59 (CVal 1 (SOff 23 0));
      YP09.mkChunk 58 (CVal 1 (SOff 23 0))]) ->
  forall j, (58 <= j < 63)%nat ->
  aview SEGS (w_H W3) (ms_mem msx) (gSH cx fp + Z.of_nat j) = Some 248.
Proof.
  intros E' ss msx HS H22 H23 Hnth j Hj.
  pose proof gb_B22 as B22. cbn [base_val] in B22.
  assert (HU23 : U E' (SOff 23 0) mod 256 = 248).
  { rewrite U_SOff, H23, (gb_EE 23%nat 23%bv eq_refl), R23, Z.add_0_r.
    unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    reflexivity. }
  destruct (st_ok_pi_region_nth E' ss _ 0%nat _ HS Hnth) as (_ & _ & _ & HC).
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite H22, B22 in HC.
  inversion HC as [|?? C62 HC1]; subst. inversion HC1 as [|?? C61 HC2]; subst.
  inversion HC2 as [|?? C60 HC3]; subst. inversion HC3 as [|?? C59 HC4]; subst.
  inversion HC4 as [|?? C58 HC5]; subst.
  cbn [ms_mem restrict] in C58, C59, C60, C61, C62.
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 62 (SOff 23 0) 248) in C62; [|exact HU23 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 61 (SOff 23 0) 248) in C61; [|exact HU23 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 60 (SOff 23 0) 248) in C60; [|exact HU23 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 59 (SOff 23 0) 248) in C59; [|exact HU23 | lia].
  apply (gb_cv1m E' (w_H W3) (ms_mem msx) _ 58 (SOff 23 0) 248) in C58; [|exact HU23 | lia].
  assert (C : (j = 58 \/ j = 59 \/ j = 60 \/ j = 61 \/ j = 62)%nat) by lia.
  destruct C as [-> | [-> | [-> | [-> | ->]]]]; cbn [Z.of_nat Pos.of_succ_nat]; assumption.
Qed.

Lemma gb_rows_run : forall (E' : env) (rs : YP09.smem) (m m' : word -> option byte),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 22 = ew gb_E 22 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  frame_of E' rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  garr8 SEGS (mrestrict (w_H W3) m) s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) ->
  garr8 SEGS (mrestrict (w_H W3) m') s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)).
Proof.
  intros E' rs m m' H9 H19 H22 Hsk HFr Hg.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & Hsp0lo & Hsp0hi & _ & _ & Hsp1 & _).
  pose proof gb_sep as (_ & HSHstk & HFstk & HSH0).
  pose proof gb_sbnd as (Hs4096 & Hsceil & _ & Hreq & Hsep & Hsepsh & Hsstk).
  pose proof gb_rows_ok as (_ & Hin1 & Hr11). pose proof gb_sweep_len as HL.
  pose proof asan_consts as (C1 & _). pose proof gb_blk as (_ & Hs0 & Hsm).
  assert (Hmb : 34 * (8 + 3 * sw_in (c_pl cx)) <= sw_mbytes (c_pl cx)).
  { pose proof HROWS as (_ & Hwant & _). unfold sw_mbytes. unfold sw_want in Hwant.
    destruct (Z.ltb_spec 0 (sw_rows (c_pl cx))); lia. }
  apply (garr8_frame SEGS (mrestrict (w_H W3) m)); [exact Hg|].
  intros a Ha. rewrite length_map in Ha. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)).
  - reflexivity.
  - intros Hw. rewrite unsigned_lit_small in Hw by lia.
    destruct (gb_wrange E' rs H9 H19 H22 Hsk a Hw) as [Hsh | Hlit]; unfold GO_LIT in *; lia.
Qed.

Lemma gb_poll_run : forall (E' : env) (rs : YP09.smem) (m m' : word -> option byte),
  ew E' 9 = ew gb_E 9 -> ew E' 19 = ew gb_E 19 -> ew E' 22 = ew gb_E 22 ->
  YP09.skeleton rs = YP09.skeleton gb_rs0 ->
  frame_of E' rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  garr8 SEGS (mrestrict (w_H W3) m) (gF cx fp + GO_POLL) (GBz (Z.of_nat i)) ->
  garr8 SEGS (mrestrict (w_H W3) m') (gF cx fp + GO_POLL) (GBz (Z.of_nat i)).
Proof.
  intros E' rs m m' H9 H19 H22 Hsk HFr Hg.
  pose proof gb_nums as (_ & HF4096 & HFceil & _ & ESH & E8 & _).
  pose proof asan_consts as (C1 & _).
  apply (garr8_frame SEGS (mrestrict (w_H W3) m)); [exact Hg|].
  intros a Ha. rewrite ipb_gbz_len in Ha. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)).
  - reflexivity.
  - intros Hw. rewrite unsigned_lit_small in Hw by (unfold GO_POLL in Ha; lia).
    destruct (gb_wrange E' rs H9 H19 H22 Hsk a Hw) as [Hsh | Hlit].
    + apply (gb_sh_nf a Hsh). unfold GO_POLL in Ha. lia.
    + unfold GO_LIT, GO_POLL in *. lia.
Qed.

Lemma gb_seat : st_ok_pi SEGS VAL gb_E ss_gb0 (restrict (w_H W3) ms3).
Proof.
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & Hsp0lo & Hsp0hi & Hsp0al & Hsp1al & Hsp1 & Hsp1al16).
  pose proof gb_B22 as B22. pose proof gb_B9 as B9. pose proof gb_B19 as B19.
  pose proof HJ as (HAR & _).
  pose proof HBODY as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & HREGS & _).
  pose proof HBLK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S96 & _).
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR Hfin) as (_ & _ & HFpres & HFSpres).
  rewrite gb_frame_eq in HFpres, HFSpres. fold (gF cx fp) in HFpres, HFSpres.
  change (fs_frame_bytes GE_CID) with 1024 in HFpres. change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres.
  pose proof asan_consts as (C1 & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia. unfold GE_STK in Hsp0lo.
  rewrite (gb_ms_eta ms3 Hfr Hfc Hsvc Hrv Hrom) at 1. rewrite Hpc, restrict_mkst_fx.
  change (w64 (BASE + GPS_gbhd)) with (Z_to_bv 64 (BASE + GPS_gbhd)).
  unfold ss_gb0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold gb_rs0. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite B22. split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (gSH cx fp + o) with (shadow_addr (gF cx fp) + o) by (rewrite ESH; unfold shadow_addr; reflexivity).
      apply (proj1 (HFSpres o ltac:(lia))).
    + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS gb_E _ (c_sp1 cx) 96 8 (SOff 19 80) (gF cx fp + GO_LIT)).
      * rewrite denot_lit_U, U_SOff, (gb_EE 19%nat 19%bv eq_refl), R19. unfold w64.
        rewrite unsigned_lit_small by (unfold GO_POLL; lia).
        rewrite zcanon_id by (unfold M64, GO_POLL; lia). unfold GO_LIT, GO_POLL. f_equal; lia.
      * cbn. unfold GO_LIT. lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. unfold gslot in S96.
        exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S96).
    + rewrite B19. split; [unfold GO_POLL; lia|]. split; [unfold GO_POLL; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (gF cx fp + GO_POLL + o) with (gF cx fp + (GO_POLL + o)) by lia.
      apply (proj1 (HFpres (gF cx fp + (GO_POLL + o)) ltac:(unfold GO_POLL; lia))).
  - unfold gb_rs0. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B22, B9, B19, ESH.
    unfold SHADOW_OFF, GO_POLL, GE_STK in *. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* One turn of the loop, 0x811f8 back to 0x811f8 (or on to 0x81298 after the sixth). *)
Lemma gb_turn : SRr SEGS W3 (mkCfg ms3 md3) (ge_post B MT cx).
Proof.
  pose proof gb_nums as (HFal & HF4096 & HFceil & HFia & ESH & E8 & Hsp0lo & Hsp0hi & Hsp0al & Hsp1al & Hsp1 & Hsp1al16).
  pose proof gb_B22 as B22. pose proof gb_B9 as B9. pose proof gb_B19 as B19.
  pose proof asan_consts as (C1 & _). unfold GE_STK in Hsp0lo.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
  pose proof HBODY as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & HREGS & _).
  pose proof HREGS as (Q2 & Q8 & Q9 & Q3 & Q4).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof gb_seat as HS.
  assert (HEI : img_env VAL A_LIM gb_E) by apply Eimg_env.
  pose proof HJ as HJ0.
  paj_run_shc RUNP RUNC HS HJ0.
  - apply gb_awr; [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity].
  - (* at reac_ctrl_identity_poll_block *)
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
    prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in P2.
    rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in P3.
    rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in P4.
    rewrite (gb_EE 18%nat 18%bv eq_refl), R18 in P10.
    rewrite (gb_EE 19%nat 19%bv eq_refl), R19 in P11.
    (* the five shadow bytes of `poll` the turn has just written *)
    assert (HR0 : region_ok SEGS gb_E (mrestrict (w_H W3) (ms_mem ms))
      (YP09.mkRegion (Some 22%nat) 58 63 58 63
         [YP09.mkChunk 62 (CVal 1 (SLit 2)); YP09.mkChunk 61 (CVal 1 (SLit 0));
          YP09.mkChunk 60 (CVal 1 (SLit 0)); YP09.mkChunk 59 (CVal 1 (SLit 0));
          YP09.mkChunk 58 (CVal 1 (SLit 0))]))
      by (refine (st_ok_region_nth gb_E _ _ 0%nat _ HS _); vm_compute; reflexivity).
    destruct HR0 as (_ & _ & _ & HC). cbn [YP09.r_base YP09.r_chunks] in HC. rewrite B22 in HC.
    inversion HC as [|?? C62 HC1]; subst. inversion HC1 as [|?? C61 HC2]; subst.
    inversion HC2 as [|?? C60 HC3]; subst. inversion HC3 as [|?? C59 HC4]; subst.
    inversion HC4 as [|?? C58 HC5]; subst. clear HC HC1 HC2 HC3 HC4 HC5.
    apply (gb_cv1 gb_E (w_H W3) (ms_mem ms) (gSH cx fp) 62 2) in C62; [|lia].
    apply (gb_cv1 gb_E (w_H W3) (ms_mem ms) (gSH cx fp) 61 0) in C61; [|lia].
    apply (gb_cv1 gb_E (w_H W3) (ms_mem ms) (gSH cx fp) 60 0) in C60; [|lia].
    apply (gb_cv1 gb_E (w_H W3) (ms_mem ms) (gSH cx fp) 59 0) in C59; [|lia].
    apply (gb_cv1 gb_E (w_H W3) (ms_mem ms) (gSH cx fp) 58 0) in C58; [|lia].
    assert (HSH5 : gb_sh5 (ms_mem ms)) by (repeat split; assumption).
    (* the frame at this state *)
    assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
    pose proof (proj1 HJ0) as HAR1.
    destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR1 Hfin) as (_ & _ & HFpres1 & _).
    rewrite gb_frame_eq in HFpres1. fold (gF cx fp) in HFpres1.
    change (fs_frame_bytes GE_CID) with 1024 in HFpres1.
    pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms) _ GE_CID fp HAR1 Hfin) as HOI.
    rewrite gb_frame_eq in HOI. fold (gF cx fp) in HOI. change (fs_frame_bytes GE_CID) with 1024 in HOI.
    pose proof (pa_obj_img 19%nat ltac:(lia)) as HO19. pose proof (pa_obj_img 6%nat ltac:(lia)) as HO6.
    assert (HM8 : gF cx fp mod 8 = 0)
      by (rewrite <- E8; replace (8 * (gF cx fp / 8)) with ((gF cx fp / 8) * 8) by lia; apply Z_mod_mult).
    pose proof (gb_ra_of_sh5 _ HSH5) as HRA.
    assert (Hsp : spZ (ms_regs ms) = c_sp1 cx)
      by (unfold spZ; rewrite P2; apply unsigned_lit_small; lia).
    pmkst HS. rewrite pa_sigma_reac_ctrl_identity_poll_block.
    eapply SRr_bind.
    {
      eapply (TIPB GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
                [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (Z.of_nat i) (gF cx fp + GO_POLL) HJ0).
      - exact (gb_rod _ _ _ HJ0).
      - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
      - unfold raZ. rewrite P1, unsigned_lit_small by (pose proof pa_B_ok as (HB1 & HB2 & _); lia).
        pose proof pa_base_lo. lia.
      - exact P3.
      - exact P4.
      - exact P10.
      - lia.
      - exact P11.
      - rewrite Hsp. exact Hsp1al16.
      - rewrite Hsp. unfold TIPB_STK, GE_STK, ESTACK. lia.
      - rewrite Hsp. lia.
      - right. rewrite Hsp. unfold TIPB_STK, ESTACK, GO_POLL. lia.
      - intros a Ha. split.
        + right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
          rewrite gb_frame_eq. fold (gF cx fp). unfold in_zr. cbn [fst snd].
          change (fs_frame_bytes GE_CID) with 1024. unfold GO_POLL in Ha. lia.
        + apply (proj1 (HFpres1 a ltac:(unfold GO_POLL in Ha; lia))).
      - assert (HGl : 65536 + 64 <= VAL (A_OBJ 19)) by exact HGB_lo.
        assert (HGh : VAL (A_OBJ 19) + 204 + 64 <= 6266880) by exact HGB_hi.
        unfold A_GRANT_GROUPB, GO_POLL. unfold off_img in HOI. lia.
      - apply (amem_range_sub_app (gF cx fp) 1024); unfold GO_POLL; [exact HFia | lia | lia | lia | lia].
      - exact HRA.
      - apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ GE_CID fp (gF cx fp + GO_POLL) 34 HAR1 Hfin);
          [ rewrite gb_frame_eq; fold (gF cx fp); unfold GO_POLL; lia
          | rewrite gb_frame_eq; fold (gF cx fp); change (fs_frame_bytes GE_CID) with 1024; unfold GO_POLL; lia
          | lia ].
      - exact (HGB _ _ (gb_rod _ _ _ HJ0)).
      - exact HGB_in.
      - exact HGB_lo.
      - exact HGB_hi. }
    cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HKEEP2 & HPOST2).
    assert (Hib : ((0 <=? Z.of_nat i) && (Z.of_nat i <=? 5))%bool = true)
      by (apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite Hib in HPOST2. destruct HPOST2 as (HA0 & HPOLLB).
    rewrite P1.
    pose proof (proj1 HJ2) as HAR2.
    destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR2 Hfin) as (_ & _ & HFpres2 & HFSpres2).
    rewrite gb_frame_eq in HFpres2, HFSpres2. fold (gF cx fp) in HFpres2, HFSpres2.
    change (fs_frame_bytes GE_CID) with 1024 in HFpres2.
    change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres2.
    pose proof gb_sep as (HSEP & HSHstk & HFstk & HSH0).
    assert (HTS : TIPB_STK = 4112) by reflexivity. unfold tipb_kept in HKEEP2.
    rewrite HTS in HKEEP2. rewrite Hsp in HKEEP2.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
      jafter_call_keep_hi HS K regs2 (mrestrict (w_H W3) mem2) HP2 [0;1;2]%nat HS2
    end.
    lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q) end.
    { apply gb_kept; try reflexivity.
      - intros a Ha. apply HKEEP2;
          [ lia | lia | intros HC; apply (gb_sh_nf a Ha); unfold GO_POLL in HC; lia ].
      - intros a Ha. apply HKEEP2; unfold GO_POLL; lia.
      - intros a Ha. apply HKEEP2; unfold GO_LIT, GO_POLL in Ha |- *; lia.
      - intros a Ha.
        replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
        apply (proj1 (HFSpres2 (a - gSH cx fp) ltac:(lia))).
      - intros a Ha. replace a with (gF cx fp + (a - gF cx fp)) by lia.
        apply (proj1 (HFpres2 (gF cx fp + (a - gF cx fp)) ltac:(unfold GO_LIT in Ha; lia))). }
    specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    (* the sweep rows and the five shadow bytes cross the call *)
    assert (HRW : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) s
                    (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
      by (apply (gb_rows_run gb_E (ss_mem ss_gb0) (ms_mem ms3));
          [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HFr
           | exact (proj2 (proj2 HROWS))]).
    assert (HTK : gb_tkeep (ms_mem ms3) (ms_mem ms))
      by (refine (gb_tkeep_run gb_E (ss_mem ss_gb0) (ms_mem ms3) (ms_mem ms) _ _ _ _ HFr);
          [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity]).
    assert (HMEM2 : gb_mem mem2).
    { apply (gb_mem_tr (ms_mem ms)); [split; [exact HSH5 | exact HRW]|].
      intros a Ha H1 H2. apply HKEEP2; [lia | lia | exact H2]. }
    assert (HTK2 : gb_tkeep (ms_mem ms3) mem2)
      by (eapply gb_tkeep_trans; [exact HTK |
          apply gb_tkeep_of_keep; intros a Ha Aa Bb; apply HKEEP2; [exact Ha | lia | exact Bb]]).
    clear HTK. rename HTK2 into HTK.
    pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS HA0 eq_refl) as HS3.
    clear HS. rename HS3 into HS. norm_ss HS.
    assert (HEI2 : img_env VAL A_LIM (havoc gb_E 512 (map (getr regs2) CLOB)))
      by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
    paj_run_shc RUNP RUNC HS HJ2.
    + apply gb_awr; try (apply ew_havoc_old; cbv; lia). vm_compute; reflexivity.
    + (* the first bcmp: `poll` against row 5 + i of the sweep *)
      prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2b. prreg HS (3%bv : bv 5) Q3b.
      prreg HS (4%bv : bv 5) Q4b. prreg HS (10%bv : bv 5) Q10.
      prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
      rewrite (gb_EE 19%nat 19%bv eq_refl), R19 in Q10.
      rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in Q2b.
      rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in Q3b.
      rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in Q4b.
      pose proof gb_sbnd as (Hs4096 & Hsceil & Hsapp & Hreq & Hsep & Hsepsh & Hsstk).
      pose proof gb_blk as (Hsin & Hs0 & Hsm).
      rewrite (gb_EE 27%nat 27%bv eq_refl), R27, unsigned_lit_small in Q11 by lia.
      replace (s + 190 + 34 * Z.of_nat i + -20) with (s + 170 + 34 * Z.of_nat i) in Q11 by lia.
      assert (Hsp2 : spZ (ms_regs ms0) = c_sp1 cx)
        by (unfold spZ; rewrite Q2b; apply unsigned_lit_small; lia).
      pose proof (proj1 HJ2) as HAR3.
      destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 Hfin) as (_ & _ & HFpres3 & HFSpres3).
      rewrite gb_frame_eq in HFpres3, HFSpres3. fold (gF cx fp) in HFpres3, HFSpres3.
      change (fs_frame_bytes GE_CID) with 1024 in HFpres3.
      change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres3.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR3 Hsin) as (_ & _ & _ & _ & Hspres3 & _).
      assert (HSH5b : gb_sh5 (ms_mem ms0))
        by (apply (gb_sh5_of_state _ _ _ HS); [apply ew_havoc_old; cbv; lia | vm_compute; reflexivity]).
      assert (HRWb : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms0)) s
                       (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t))).
      { refine (gb_rows_run _ _ mem2 _ _ _ _ _ HFr0 (proj2 HMEM2));
        [ apply ew_havoc_old; cbv; lia | apply ew_havoc_old; cbv; lia
        | apply ew_havoc_old; cbv; lia | vm_compute; reflexivity ]. }
      assert (HTK3 : gb_tkeep (ms_mem ms3) (ms_mem ms0))
        by (eapply gb_tkeep_trans; [exact HTK |
            refine (gb_tkeep_run _ _ mem2 _ _ _ _ _ HFr0);
            [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
      clear HTK. rename HTK3 into HTK.
      pmkst HS.
      eapply SRr_bind.
      { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA GS___interceptor_trampoline_bcmp) ABCMP
                  W3 (ms_regs ms0) (ms_mem ms0) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
                  (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k
                  (gF cx fp + GO_POLL) (s + 170 + 34 * Z.of_nat i) 34
                  (c_sp1 cx - spZ (c_regs cx)) _ HJ2).
        - exact Q10.
        - exact Q11.
        - exact Q12.
        - lia.
        - unfold GO_POLL. lia.
        - unfold GO_POLL. lia.
        - lia.
        - lia.
        - rewrite Hsp2. lia.
        - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
        - lia.
        - unfold ESTACK, GE_STK. lia.
        - exact Q3b.
        - exact Q4b.
        - exact Q1.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - intros a Ha. split.
          + apply (aview_some_of_apresent SEGS).
            replace a with (gF cx fp + (a - gF cx fp)) by lia.
            apply (proj1 (HFpres3 (gF cx fp + (a - gF cx fp)) ltac:(unfold GO_POLL in Ha; lia))).
          + rewrite Hsp2. unfold ESTACK, GO_POLL in *. lia.
        - intros a Ha. split.
          + apply (aview_some_of_apresent SEGS). apply (proj1 (Hspres3 a ltac:(lia))).
          + rewrite Hsp2. unfold ESTACK. lia.
        - intros a Ha. unfold ESTACK, GO_POLL in *. lia.
        - intros a Ha. unfold ESTACK in *. lia.
        - apply (amem_range_sub_app (gF cx fp) 1024); unfold GO_POLL; [exact HFia | lia | lia | lia | lia].
        - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ s (sw_mbytes (c_pl cx)) _ 34
                   HAR3 Hsin); lia.
        - exact (gb_ra_of_sh5 _ HSH5b).
        - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ GE_CID fp
                             (gF cx fp + GO_POLL) 34 HAR3 Hfin);
            [ rewrite gb_frame_eq; fold (gF cx fp); unfold GO_POLL; lia
            | rewrite gb_frame_eq; fold (gF cx fp); change (fs_frame_bytes GE_CID) with 1024;
              unfold GO_POLL; lia
            | lia ].
        - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ s (sw_mbytes (c_pl cx))
                   _ 34 HAR3 Hsin); lia.
        - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ s
                             (sw_mbytes (c_pl cx)) _ 34 HAR3 Hsin); lia. }
      cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & v4 & -> & HJ4 & HP4 & Hv4 & Hcmp4 & Hkp4 & Hpr4).
      (* the bytes agree, so the branch to the error path is not taken *)
      assert (HPOLLBb : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms0)) (gF cx fp + GO_POLL) (GBz (Z.of_nat i))).
      { refine (gb_poll_run _ _ mem2 _ _ _ _ _ HFr0 HPOLLB);
        [ gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity ]. }
      assert (Hv40 : v4 = w64 0)
        by (apply Hcmp4; intros j Hj; apply gb_row_eq; [exact HPOLLBb | exact HRWb | lia]).
      rewrite Hv40 in Hv4.
      assert (HSH5c : gb_sh5 mem4)
        by (apply (gb_sh5_tr (ms_mem ms0)); [exact HSH5b | intros a Ha; apply Hkp4; unfold ESTACK; lia]).
      assert (HRWc : garr8 SEGS (mrestrict (w_H W3) mem4) s
                       (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
        by (apply (gb_garr8_tr (ms_mem ms0)); [exact HRWb|];
            intros a Ha; rewrite length_map in Ha; pose proof gb_rowlen as HRL;
            apply Hkp4; unfold ESTACK; lia).
      assert (HTK4 : gb_tkeep (ms_mem ms3) mem4)
        by (eapply gb_tkeep_trans; [exact HTK |
            intros a Ha Aa Bb Cc Dd; apply Hkp4; [exact Ha | unfold ESTACK; lia]]).
      clear HTK. rename HTK4 into HTK.
      lazymatch type of HS with st_ok _ _ ?ss _ =>
        let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
        jafter_call_keep_hi HS K regs4 (mrestrict (w_H W3) mem4) HP4 [0;1;2]%nat HS4
      end.
      lazymatch type of HS4 with ?Q -> _ => assert (HQ4 : Q) end.
      { apply gb_kept; try gb_ewold.
        - intros a Ha. apply Hkp4; unfold ESTACK; lia.
        - intros a Ha. apply Hkp4; unfold ESTACK; lia.
        - intros a Ha. apply Hkp4; unfold GO_LIT in Ha; unfold ESTACK; lia.
        - intros a Ha. apply Hpr4.
          replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
          apply (proj1 (HFSpres3 (a - gSH cx fp) ltac:(lia))).
        - intros a Ha. apply Hpr4. replace a with (gF cx fp + (a - gF cx fp)) by lia.
          apply (proj1 (HFpres3 (gF cx fp + (a - gF cx fp)) ltac:(unfold GO_LIT in Ha; lia))). }
      specialize (HS4 HQ4). clear HQ4 HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
      pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS Hv4 eq_refl) as HS5.
      clear HS. rename HS5 into HS. norm_ss HS.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HEI3 : img_env VAL A_LIM Ev)
          by (repeat (apply img_env_havoc_hi; [|cbv; lia]); exact HEI)
      end.
      paj_run_shc RUNP RUNC HS HJ4.
      * apply gb_awr; try gb_ewold; try (vm_compute; reflexivity).
      * (* the second bcmp: row 5 + i at 16 against the compound literal *)
        prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3.
        prreg HS (4%bv : bv 5) U4. prreg HS (10%bv : bv 5) U10.
        prreg HS (11%bv : bv 5) U11. prreg HS (12%bv : bv 5) U12.
        rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in U2.
        rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in U3.
        rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in U4.
        rewrite (gb_EE 27%nat 27%bv eq_refl), R27, unsigned_lit_small in U10 by lia.
        replace (s + 190 + 34 * Z.of_nat i + -4) with (s + 170 + 34 * Z.of_nat i + 16) in U10 by lia.
        rewrite (gb_EE 19%nat 19%bv eq_refl), R19, unsigned_lit_small in U11 by (unfold GO_POLL; lia).
        replace (gF cx fp + GO_POLL + 80) with (gF cx fp + GO_LIT) in U11 by (unfold GO_POLL, GO_LIT; lia).
        assert (Hsp3 : spZ (ms_regs ms1) = c_sp1 cx)
          by (unfold spZ; rewrite U2; apply unsigned_lit_small; lia).
        pose proof (proj1 HJ4) as HAR5.
        destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR5 Hfin) as (_ & _ & HFpres5 & HFSpres5).
        rewrite gb_frame_eq in HFpres5, HFSpres5. fold (gF cx fp) in HFpres5, HFSpres5.
        change (fs_frame_bytes GE_CID) with 1024 in HFpres5.
        change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres5.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR5 Hsin)
          as (_ & _ & _ & _ & Hspres5 & _).
        assert (HTK5 : gb_tkeep (ms_mem ms3) (ms_mem ms1))
          by (eapply gb_tkeep_trans; [exact HTK |
              refine (gb_tkeep_run _ _ mem4 _ _ _ _ _ HFr1);
              [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]).
        clear HTK. rename HTK5 into HTK.
        assert (HRWd : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms1)) s
                         (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
          by (refine (gb_rows_run _ _ mem4 _ _ _ _ _ HFr1 HRWc);
              [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
        assert (HL4 : forall j, 0 <= j < 4 ->
                  aview SEGS (w_H W3) (ms_mem ms1) (gF cx fp + GO_LIT + j) = Some (nth (Z.to_nat j) LITz 0))
          by (apply (gb_lit4_of_state _ _ _ HS);
              [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
        pmkst HS.
        eapply SRr_bind.
        { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA GS___interceptor_trampoline_bcmp) ABCMP
                    W3 (ms_regs ms1) (ms_mem ms1) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
                    (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k
                    (s + 170 + 34 * Z.of_nat i + 16) (gF cx fp + GO_LIT) 4
                    (c_sp1 cx - spZ (c_regs cx)) _ HJ4).
          - exact U10.
          - exact U11.
          - exact U12.
          - lia.
          - lia.
          - lia.
          - unfold GO_LIT. lia.
          - unfold GO_LIT. lia.
          - rewrite Hsp3. lia.
          - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
          - lia.
          - unfold ESTACK, GE_STK. lia.
          - exact U3.
          - exact U4.
          - exact U1.
          - apply ret_ok_codeptr_v; [lia | reflexivity].
          - intros a Ha. split.
            + apply (aview_some_of_apresent SEGS). apply (proj1 (Hspres5 a ltac:(lia))).
            + rewrite Hsp3. unfold ESTACK. lia.
          - intros a Ha. split.
            + apply (aview_some_of_apresent SEGS). replace a with (gF cx fp + (a - gF cx fp)) by lia.
              apply (proj1 (HFpres5 (gF cx fp + (a - gF cx fp)) ltac:(unfold GO_LIT in Ha; lia))).
            + rewrite Hsp3. unfold ESTACK, GO_LIT in *. lia.
          - intros a Ha. unfold ESTACK in *. lia.
          - intros a Ha. unfold ESTACK, GO_LIT in *. lia.
          - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ s (sw_mbytes (c_pl cx))
                     _ 4 HAR5 Hsin); lia.
          - apply (amem_range_sub_app (gF cx fp) 1024); unfold GO_LIT; [exact HFia | lia | lia | lia | lia].
          - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ s
                     (sw_mbytes (c_pl cx)) _ 4 HAR5 Hsin); lia.
          - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ s
                               (sw_mbytes (c_pl cx)) _ 4 HAR5 Hsin); lia.
          - apply gb_ra_lit. apply gb_sh68. exact HTK.
          - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ GE_CID fp
                               (gF cx fp + GO_LIT) 4 HAR5 Hfin);
              [ rewrite gb_frame_eq; fold (gF cx fp); unfold GO_LIT; lia
              | rewrite gb_frame_eq; fold (gF cx fp); change (fs_frame_bytes GE_CID) with 1024;
                unfold GO_LIT; lia
              | lia ]. }
        cbv beta.
        intros W6 c6 Hwle6 (-> & regs6 & mem6 & md6 & v6 & -> & HJ6 & HP6 & Hv6 & Hcmp6 & Hkp6 & Hpr6).
        assert (Hv60 : v6 = w64 0)
          by (apply Hcmp6; intros j Hj; apply gb_lit_eq; [exact HRWd | exact HL4 | lia]).
        rewrite Hv60 in Hv6.
        assert (HTK6 : gb_tkeep (ms_mem ms3) mem6)
          by (eapply gb_tkeep_trans; [exact HTK |
              intros a Ha Aa Bb Cc Dd; apply Hkp6; [exact Ha | unfold ESTACK; lia]]).
        clear HTK. rename HTK6 into HTK.
        assert (HRWe : garr8 SEGS (mrestrict (w_H W3) mem6) s
                         (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
          by (apply (gb_garr8_tr (ms_mem ms1)); [exact HRWd|];
              intros a Ha; rewrite length_map in Ha; pose proof gb_rowlen as HRL;
              apply Hkp6; unfold ESTACK; lia).
        lazymatch type of HS with st_ok _ _ ?ss _ =>
          let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
          jafter_call_keep_hi HS K regs6 (mrestrict (w_H W3) mem6) HP6 [0;1;2]%nat HS6
        end.
        lazymatch type of HS6 with ?Q -> _ => assert (HQ6 : Q) end.
        { apply gb_kept; try gb_ewold.
          - intros a Ha. apply Hkp6; unfold ESTACK; lia.
          - intros a Ha. apply Hkp6; unfold ESTACK; lia.
          - intros a Ha. apply Hkp6; unfold GO_LIT in Ha; unfold ESTACK; lia.
          - intros a Ha. apply Hpr6.
            replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
            apply (proj1 (HFSpres5 (a - gSH cx fp) ltac:(lia))).
          - intros a Ha. apply Hpr6. replace a with (gF cx fp + (a - gF cx fp)) by lia.
            apply (proj1 (HFpres5 (gF cx fp + (a - gF cx fp)) ltac:(unfold GO_LIT in Ha; lia))). }
        specialize (HS6 HQ6). clear HQ6 HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
        pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS Hv6 eq_refl) as HS7.
        clear HS. rename HS7 into HS. norm_ss HS.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HEI4 : img_env VAL A_LIM Ev)
            by (repeat (apply img_env_havoc_hi; [|cbv; lia]); exact HEI)
        end.
        paj_run_shc RUNP RUNC HS HJ6.
        ** apply gb_awr; try gb_ewold; try (vm_compute; reflexivity).
        ** (* the third bcmp: row 5 + i at 20 against POLL[i] of the image *)
           prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3.
           prreg HS (4%bv : bv 5) V4. prreg HS (10%bv : bv 5) V10.
           prreg HS (11%bv : bv 5) V11. prreg HS (12%bv : bv 5) V12.
           rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in V2.
           rewrite (gb_EE 3%nat 3%bv eq_refl), Q3, Hgp in V3.
           rewrite (gb_EE 4%nat 4%bv eq_refl), Q4, Htp in V4.
           rewrite (gb_EE 27%nat 27%bv eq_refl), R27 in V10.
           replace (s + 190 + 34 * Z.of_nat i) with (s + 170 + 34 * Z.of_nat i + 20) in V10 by lia.
           rewrite (gb_EE 26%nat 26%bv eq_refl), R26 in V11.
           assert (Hsp4 : spZ (ms_regs ms2) = c_sp1 cx)
             by (unfold spZ; rewrite V2; apply unsigned_lit_small; lia).
           pose proof (proj1 HJ6) as HAR7.
           destruct (al_blocks _ _ LAWS _ _ _ _ _ s (sw_mbytes (c_pl cx)) HAR7 Hsin)
             as (_ & _ & _ & _ & Hspres7 & _).
           assert (HRWf : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms2)) s
                            (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
             by (refine (gb_rows_run _ _ mem6 _ _ _ _ _ HFr2 HRWe);
                 [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]).
           pose proof (HPOLL _ _ (gb_rod _ _ _ HJ6)) as HPT.
           pose proof (pa_obj_img 6%nat ltac:(lia)) as HO6'.
           assert (HPl : 65536 + 64 <= VAL (A_OBJ 6)) by exact HPOLL_lo.
           assert (HPh : VAL (A_OBJ 6) + 18 + 64 <= 6266880) by exact HPOLL_hi.
           assert (HROP : range_addressable (aview SEGS (w_H W3) (ms_mem ms2)) SHADOW_OFF
                            (VAL (A_OBJ 6) + 3 * Z.of_nat i) 3 /\
                          shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms2)) (VAL (A_OBJ 6) + 3 * Z.of_nat i) 3).
           { eapply ro_read_ok_glob; [exact HGM | exact HPOLL_in | exact HIMGSH | exact HAR7 | lia | lia | lia
               | apply (Z.le_trans _ (VAL (A_OBJ 6))); [exact HPOLL_lo | lia]
               | apply (Z.le_trans _ (VAL (A_OBJ 6) + 18 + 64)); [lia | exact HPOLL_hi]]. }
           destruct HROP as (HRAP & HHUP).
           pmkst HS.
           eapply SRr_bind.
           { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA GS___interceptor_trampoline_bcmp) ABCMP
                       W3 (ms_regs ms2) (ms_mem ms2) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
                       (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k
                       (s + 170 + 34 * Z.of_nat i + 20) (VAL (A_OBJ 6) + 3 * Z.of_nat i) 3
                       (c_sp1 cx - spZ (c_regs cx)) _ HJ6).
             - exact V10.
             - exact V11.
             - exact V12.
             - lia.
             - lia.
             - lia.
             - lia.
             - lia.
             - rewrite Hsp4. lia.
             - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
             - lia.
             - unfold ESTACK, GE_STK. lia.
             - exact V3.
             - exact V4.
             - exact V1.
             - apply ret_ok_codeptr_v; [lia | reflexivity].
             - intros a Ha. split.
               + apply (aview_some_of_apresent SEGS). apply (proj1 (Hspres7 a ltac:(lia))).
               + rewrite Hsp4. unfold ESTACK. lia.
             - intros a Ha. split.
               + destruct (garr8_nthZ SEGS _ _ _ (a - VAL (A_OBJ 6)) HPT ltac:(lia)
                             ltac:(cbn [length POLLz]; lia)) as (Hva & Hra).
                 replace (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) with a in Hva by lia.
                 rewrite (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms2) _ _ Hva Hra). discriminate.
               + rewrite Hsp4. unfold ESTACK. lia.
             - intros a Ha. unfold ESTACK in *. lia.
             - intros a Ha. unfold ESTACK in *. lia.
             - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ s (sw_mbytes (c_pl cx))
                        _ 3 HAR7 Hsin); lia.
             - unfold amem_range, kLowMemEnd. left. lia.
             - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ s
                        (sw_mbytes (c_pl cx)) _ 3 HAR7 Hsin); lia.
             - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ s
                                  (sw_mbytes (c_pl cx)) _ 3 HAR7 Hsin); lia.
             - exact HRAP.
             - intros _. exact HHUP. }
           cbv beta.
           intros W8 c8 Hwle8 (-> & regs8 & mem8 & md8 & v8 & -> & HJ8 & HP8 & Hv8 & Hcmp8 & Hkp8 & Hpr8).
           assert (Hv80 : v8 = w64 0)
             by (apply Hcmp8; intros j Hj; apply gb_pollt_eq; [exact HRWf | exact HPT | lia]).
           rewrite Hv80 in Hv8.
           assert (HTK8 : gb_tkeep (ms_mem ms3) mem8)
             by (eapply gb_tkeep_trans; [exact HTK |
                 eapply gb_tkeep_trans; [refine (gb_tkeep_run _ _ mem6 _ _ _ _ _ HFr2);
                                         [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity] |
                 intros a Ha Aa Bb Cc Dd; apply Hkp8; [exact Ha | unfold ESTACK; lia]]]).
           clear HTK. rename HTK8 into HTK.
           assert (HRWg : garr8 SEGS (mrestrict (w_H W3) mem8) s
                            (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)))
             by (apply (gb_garr8_tr (ms_mem ms2)); [exact HRWf|];
                 intros a Ha; rewrite length_map in Ha; pose proof gb_rowlen as HRL;
                 apply Hkp8; unfold ESTACK; lia).
           destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR7 Hfin) as (_ & _ & HFpres7 & HFSpres7).
           rewrite gb_frame_eq in HFpres7, HFSpres7. fold (gF cx fp) in HFpres7, HFSpres7.
           change (fs_frame_bytes GE_CID) with 1024 in HFpres7.
           change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres7.
           lazymatch type of HS with st_ok _ _ ?ss _ =>
             let K := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) in
             jafter_call_keep_hi HS K regs8 (mrestrict (w_H W3) mem8) HP8 [0;1;2]%nat HS8
           end.
           lazymatch type of HS8 with ?Q -> _ => assert (HQ8 : Q) end.
           { apply gb_kept; try gb_ewold.
             - intros a Ha. apply Hkp8; unfold ESTACK; lia.
             - intros a Ha. apply Hkp8; unfold ESTACK; lia.
             - intros a Ha. apply Hkp8; unfold GO_LIT in Ha; unfold ESTACK; lia.
             - intros a Ha. apply Hpr8.
               replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by (rewrite ESH; unfold shadow_addr; lia).
               apply (proj1 (HFSpres7 (a - gSH cx fp) ltac:(lia))).
             - intros a Ha. apply Hpr8. replace a with (gF cx fp + (a - gF cx fp)) by lia.
               apply (proj1 (HFpres7 (gF cx fp + (a - gF cx fp)) ltac:(unfold GO_LIT in Ha; lia))). }
           specialize (HS8 HQ8). clear HQ8 HS. rewrite <- restrict_mkst_fx in HS8. rename HS8 into HS.
           pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS Hv8 eq_refl) as HS9.
           clear HS. rename HS9 into HS. norm_ss HS.
           lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
             assert (HEI5 : img_env VAL A_LIM Ev)
               by (repeat (apply img_env_havoc_hi; [|cbv; lia]); exact HEI)
           end.
           paj_run_shc RUNP RUNC HS HJ8.
           *** apply gb_awr; try gb_ewold; try (vm_compute; reflexivity).
           *** psrr_branch_pi RUNP BR HS.
               ---- (* the counter is not zero: one more turn *)
                 rewrite branch_ne_U, U_SOff, U_SLit in Hc.
                 rewrite !ew_havoc_old in Hc by (cbv; lia).
                 rewrite (gb_EE 21%nat 21%bv eq_refl), R21, unsigned_lit_small in Hc by lia.
                 rewrite zcanon_id in Hc by (unfold M64; lia).
                 change (zcanon 0) with 0 in Hc.
                 apply (proj1 (negb_true_iff _)) in Hc. apply (proj1 (Z.eqb_neq _ _)) in Hc.
                 assert (Hi5 : (i < 5)%nat) by lia.
                 paj_run_to_sh RUNTOP HS HJ8 2888.
                 ++++ apply gb_awr; try gb_ewold; try (vm_compute; reflexivity).
                ++++ (* land at the head of the next turn *)
                     pose proof HBLK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & _).
                     pose proof gb_sbnd as (Hs4096' & Hsceil' & _ & Hreq' & _ & _ & _).
                     pose proof (pa_obj_img 6%nat ltac:(lia)) as HO6b.
                     pose proof HS as (HfrL & HpcL & HsvcL & HrvL & HfcL & HromL & _).
                     cbn [ss_pc abs_ss ss_resv resv_denot] in HpcL, HrvL.
                     assert (HTK9 : gb_tkeep (ms_mem ms3) (ms_mem ms5))
                       by (eapply gb_tkeep_trans; [exact HTK |
                           eapply gb_tkeep_trans;
                           [ refine (gb_tkeep_run _ _ mem8 _ _ _ _ _ HFr3);
                             [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]
                           | refine (gb_tkeep_run _ _ (ms_mem ms4) _ _ _ _ _ HFr4);
                             [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]]).
                     assert (HRWh : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms5)) s
                                      (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t))).
                     { refine (gb_rows_run _ _ (ms_mem ms4) _ _ _ _ _ HFr4 _);
                         [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity |].
                       refine (gb_rows_run _ _ mem8 _ _ _ _ _ HFr3 HRWg);
                         [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]. }
                     assert (H248 : forall j, (58 <= j < 63)%nat ->
                               aview SEGS (w_H W3) (ms_mem ms5) (gSH cx fp + Z.of_nat j) = Some 248)
                       by (apply (gb_sh5f_of_state _ _ _ HS);
                           [gb_ewold | gb_ewold | vm_compute; reflexivity]).
                     prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
                     prreg HS (8%bv : bv 5) Z8. prreg HS (9%bv : bv 5) Z9.
                     prreg HS (18%bv : bv 5) Y18. prreg HS (19%bv : bv 5) Y19.
                     prreg HS (20%bv : bv 5) Y20. prreg HS (21%bv : bv 5) Y21.
                     prreg HS (22%bv : bv 5) Y22. prreg HS (23%bv : bv 5) Y23.
                     prreg HS (24%bv : bv 5) Y24. prreg HS (25%bv : bv 5) Y25.
                     prreg HS (26%bv : bv 5) Y26. prreg HS (27%bv : bv 5) Y27.
                     rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in Z2.
                     rewrite (gb_EE 3%nat 3%bv eq_refl), Q3 in Z3.
                     rewrite (gb_EE 4%nat 4%bv eq_refl), Q4 in Z4.
                     rewrite (gb_EE 8%nat 8%bv eq_refl), Q8 in Z8.
                     rewrite (gb_EE 9%nat 9%bv eq_refl), Q9 in Z9.
                     rewrite (gb_EE 19%nat 19%bv eq_refl), R19 in Y19.
                     rewrite (gb_EE 20%nat 20%bv eq_refl), R20 in Y20.
                     rewrite (gb_EE 22%nat 22%bv eq_refl), R22 in Y22.
                     rewrite (gb_EE 23%nat 23%bv eq_refl), R23 in Y23.
                     rewrite (gb_EE 24%nat 24%bv eq_refl), R24 in Y24.
                     rewrite (gb_EE 25%nat 25%bv eq_refl), R25 in Y25.
                     rewrite (gb_EE 18%nat 18%bv eq_refl), R18 in Y18. unfold w64 in Y18.
                     rewrite (gb_addiw1 (Z.of_nat i) ltac:(lia)) in Y18.
                     rewrite (gb_EE 21%nat 21%bv eq_refl), R21, unsigned_lit_small in Y21 by lia.
                     rewrite (gb_EE 26%nat 26%bv eq_refl), R26, unsigned_lit_small in Y26 by lia.
                     rewrite (gb_EE 27%nat 27%bv eq_refl), R27, unsigned_lit_small in Y27 by lia.
                     apply (HLOOP ms5 _ ltac:(lia) HJ8).
                     ----- apply (gb_land_body ms5 GPS_gbhd);
                             [ exact HpcL | exact HrvL | exact HsvcL | exact HromL | exact HfrL | exact HfcL
                             | exact Z2 | exact Z8 | exact Z9 | exact Z3 | exact Z4 | exact HTK9 | exact H248 ].
                     ----- apply (gb_land_blk ms5 HTK9 Y20).
                     ----- apply gb_land_rows. exact HRWh.
                     ----- rewrite Y18. unfold w64. f_equal. lia.
                     ----- rewrite Y27. unfold w64. f_equal. lia.
                     ----- rewrite Y26. unfold w64. f_equal. lia.
                     ----- rewrite Y21. unfold w64. f_equal. lia.
                     ----- exact Y19.
                     ----- exact Y24.
                     ----- exact Y25.
                     ----- exact Y23.
                     ----- exact Y22.
               ---- (* the counter is zero: the sixth turn is done *)
                 rewrite branch_ne_U, U_SOff, U_SLit in Hc.
                 rewrite !ew_havoc_old in Hc by (cbv; lia).
                 rewrite (gb_EE 21%nat 21%bv eq_refl), R21, unsigned_lit_small in Hc by lia.
                 rewrite zcanon_id in Hc by (unfold M64; lia).
                 change (zcanon 0) with 0 in Hc.
                 apply (proj1 (negb_false_iff _)) in Hc. apply (proj1 (Z.eqb_eq _ _)) in Hc.
                 assert (Hi5 : i = 5%nat) by lia.
                 paj_run_to_sh RUNTOP HS HJ8 3048.
                 ++++ apply gb_awr; try gb_ewold; try (vm_compute; reflexivity).
                ++++ (* land at the free of the first sweep buffer *)
                     pose proof HBLK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & _).
                     pose proof HS as (HfrL & HpcL & HsvcL & HrvL & HfcL & HromL & _).
                     cbn [ss_pc abs_ss ss_resv resv_denot] in HpcL, HrvL.
                     assert (HTK9 : gb_tkeep (ms_mem ms3) (ms_mem ms5))
                       by (eapply gb_tkeep_trans; [exact HTK |
                           eapply gb_tkeep_trans;
                           [ refine (gb_tkeep_run _ _ mem8 _ _ _ _ _ HFr3);
                             [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]
                           | refine (gb_tkeep_run _ _ (ms_mem ms4) _ _ _ _ _ HFr4);
                             [gb_ewold | gb_ewold | gb_ewold | vm_compute; reflexivity]]]).
                     assert (H248 : forall j, (58 <= j < 63)%nat ->
                               aview SEGS (w_H W3) (ms_mem ms5) (gSH cx fp + Z.of_nat j) = Some 248)
                       by (apply (gb_sh5f_of_state _ _ _ HS);
                           [gb_ewold | gb_ewold | vm_compute; reflexivity]).
                     prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
                     prreg HS (8%bv : bv 5) Z8. prreg HS (9%bv : bv 5) Z9.
                     prreg HS (20%bv : bv 5) Y20. prreg HS (22%bv : bv 5) Y22.
                     rewrite (gb_EE 2%nat 2%bv eq_refl), Q2 in Z2.
                     rewrite (gb_EE 3%nat 3%bv eq_refl), Q3 in Z3.
                     rewrite (gb_EE 4%nat 4%bv eq_refl), Q4 in Z4.
                     rewrite (gb_EE 8%nat 8%bv eq_refl), Q8 in Z8.
                     rewrite (gb_EE 9%nat 9%bv eq_refl), Q9 in Z9.
                     rewrite (gb_EE 20%nat 20%bv eq_refl), R20 in Y20.
                     rewrite (gb_EE 22%nat 22%bv eq_refl), R22 in Y22.
                     apply (HEXIT ms5 _ HJ8).
                     ----- apply (gb_land_body ms5 GPS_free1);
                             [ exact HpcL | exact HrvL | exact HsvcL | exact HromL | exact HfrL | exact HfcL
                             | exact Z2 | exact Z8 | exact Z9 | exact Z3 | exact Z4 | exact HTK9 | exact H248 ].
                     ----- apply (gb_land_blk ms5 HTK9 Y20).
                     ----- exact Y22.
Qed.

End t.

(* ---- the loop: induction on the turns that remain, 6 - i ---- *)
Lemma gb_loop :
  ge_from B MT (ge_post B MT) (GIS_free1 B MT) ->
  forall (n : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) (t s : Z) (i : nat),
  (6 - i <= n)%nat ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  ge_body cx fp GPS_gbhd W3 ms3 GSH_a -> k <= 2 -> acc <= GE_A2 MT - mo_free MT ->
  gsw_blk B cx fp ly3 S3 W3 ms3 t s -> gsw_rows cx W3 ms3 t s ->
  (i <= 5)%nat ->
  getr (ms_regs ms3) 18 = w64 (Z.of_nat i) ->
  getr (ms_regs ms3) 27 = w64 (s + 190 + 34 * Z.of_nat i) ->
  getr (ms_regs ms3) 26 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat i) ->
  getr (ms_regs ms3) 21 = w64 (6 - Z.of_nat i) ->
  getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_POLL) ->
  getr (ms_regs ms3) 24 = w64 17 -> getr (ms_regs ms3) 25 = w64 5 ->
  getr (ms_regs ms3) 23 = w64 (-8) -> getr (ms_regs ms3) 22 = w64 (gSH cx fp) ->
  SRr SEGS W3 (mkCfg ms3 md3) (ge_post B MT cx).
Proof.
  intros HF n. induction n as [|n IH];
    intros cx fp k acc ly3 S3 W3 ms3 md3 t s i Hn HB HJ HFR HMO HBODY Hk2 Hacc HBLK HROWS Hi
      R18 R27 R26 R21 R19 R24 R25 R23 R22.
  - lia.
  - eapply gb_turn with (t := t) (s := s) (i := i); try eassumption.
    + intros ms' md' Hi' HJ' HBODY' HBLK' HROWS' R18' R27' R26' R21' R19' R24' R25' R23' R22'.
      exact (IH cx fp k acc ly3 S3 W3 ms' md' t s (S i) ltac:(lia) HB HJ' HFR HMO HBODY' Hk2 Hacc
               HBLK' HROWS' Hi' R18' R27' R26' R21' R19' R24' R25' R23' R22').
    + intros ms' md' HJ' HBODY' HBLK' R22'.
      exact (HF cx fp k acc ly3 S3 W3 ms' md' HB HJ' HFR HMO
               (ex_intro _ t (ex_intro _ s (conj HBODY' (conj Hk2 (conj Hacc (conj HBLK' R22'))))))).
Qed.

End c.

(* ---- the segment ---- *)
(* Beyond SEG_gb's own premises it takes the callee's contract, as CtrlIdentityPollBlock.v
   states it, and the image's two read-only tables it reads:
   GRANT_GROUPB (object 19), which the callee copies, and POLL (object 6). *)
Lemma gsw_seg_gb : forall (B : asyms) (MT : ameter_ops) (GLOBS : list (Z * Z)),
  globs_marked SEGS B GLOBS ->
  tctrl_identity_poll_block_spec B GLOBS ->
  In (VAL (A_OBJ 19), 204) GLOBS ->
  IMG_LO + 64 <= VAL (A_OBJ 19) -> VAL (A_OBJ 19) + 204 + 64 <= IMG_HI ->
  (forall (H : word -> bool) (mem : word -> option byte),
     arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 19)) GBallz) ->
  In (VAL (A_OBJ 6), 18) GLOBS ->
  IMG_LO + 64 <= VAL (A_OBJ 6) -> VAL (A_OBJ 6) + 18 + 64 <= IMG_HI ->
  (forall (H : word -> bool) (mem : word -> option byte),
     arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 6)) POLLz) ->
  SEG_gb B MT.
Proof.
  intros B MT GLOBS HGM TIPB HGBin HGBlo HGBhi HGB HPin HPlo HPhi HP RT HF.
  destruct RT as (LAWS & TL & _ & _ & _ & _ & _ & ABCMP & RT').
  assert (HIMGSH : img_shadow_vis SEGS B) by (first [exact RT' | exact (proj1 RT')]).
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGIS.
  destruct HGIS as (t & s & i & HBODY & Hk2 & Hacc & HBLK & HROWS & Hi
                    & R18 & R27 & R26 & R21 & R19 & R24 & R25 & R23 & R22).
  eapply gb_loop with (n := (6 - i)%nat) (t := t) (s := s) (i := i); first [eassumption | lia].
Qed.

End b.
End a.
