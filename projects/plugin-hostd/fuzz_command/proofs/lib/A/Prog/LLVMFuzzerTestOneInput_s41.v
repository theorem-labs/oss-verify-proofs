(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86718 .. 0x86770: strnlen of the message and the three mallocs), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import ConstsViewDef StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaDenot CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01
LLVMFuzzerTestOneInput_s40.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords SlotWordsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- lists ---- *)
Lemma aw_nth_firstn_loc : forall {A} (l : list A) m i d, (i < m)%nat -> nth i (firstn m l) d = nth i l d.
Proof.
intros A l. induction l as [|a l IH]; intros [|m] [|i] d Hi; cbn [firstn nth]; try reflexivity; try lia.
apply IH. lia.
Qed.
Lemma aw_nodup_snoc_loc : forall {A} (l : list A) x, List.NoDup (l ++ [x]) -> ~ In x l.
Proof.
intros A l. induction l as [|a l IH]; intros x H Hin; [destruct Hin|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hn Hd]. destruct Hin as [<- | Hin].
- apply Hn, in_or_app. right. left. reflexivity.
- exact (IH x Hd Hin).
Qed.
Lemma aw_nth_map_loc : forall (l : list byte) j, (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l. induction l as [|b l IH]; intros [|j] Hj; cbn [length] in Hj; try lia; cbn [map nth]; [reflexivity|].
apply IH. lia.
Qed.

(* strnlen's answer: the first NUL of the message's bytes, or their count when none is NUL, is the length of the
   message up to its first NUL (the plain model's Verbs.upto0) *)
Lemma aw_first_nul_loc : forall (rd : reader) D x k,
  abytes_atR rd x D -> 0 <= k <= Z.of_nat (length D) ->
  (forall i, 0 <= i < k -> exists b, rd (x + i) = Some b /\ b <> 0) ->
  (k < Z.of_nat (length D) -> rd (x + k) = Some 0) ->
  k = Z.of_nat (length (Verbs.upto0 D)).
Proof.
intros rd D. induction D as [|b D IH]; intros x k HD Hk Hb Hz.
- cbn [length Z.of_nat] in Hk. cbn. lia.
- assert (H0 : rd x = Some (bv_unsigned b)).
  { pose proof (HD 0%nat ltac:(cbn [length]; lia)) as H. rewrite Z.add_0_r in H. exact H. }
  unfold Verbs.upto0. cbn [Verbs.upto].
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
  + cbn [length Z.of_nat].
    destruct (Z.eq_dec k 0) as [->|Hne]; [reflexivity|]. exfalso.
    destruct (Hb 0 ltac:(lia)) as (b' & Hb' & Hn). rewrite Z.add_0_r, H0 in Hb'. injection Hb' as <-. exact (Hn E).
  + cbn [length]. rewrite Nat2Z.inj_succ.
    destruct (Z.eq_dec k 0) as [->|Hne].
    * exfalso. cbn [length] in Hz. pose proof (Hz ltac:(lia)) as H. rewrite Z.add_0_r, H0 in H.
      injection H as H. exact (E H).
    * assert (IHk : k - 1 = Z.of_nat (length (Verbs.upto0 D))).
      { apply (IH (x + 1) (k - 1)).
        - intros i Hi. replace (x + 1 + Z.of_nat i) with (x + Z.of_nat (S i)) by lia.
          rewrite (HD (S i) ltac:(cbn [length]; lia)). reflexivity.
        - cbn [length] in Hk. lia.
        - intros i Hi. replace (x + 1 + i) with (x + (i + 1)) by lia. apply Hb. lia.
        - intros Hl. replace (x + 1 + (k - 1)) with (x + k) by lia. apply Hz. cbn [length]. lia. }
      unfold Verbs.upto0 in IHk. lia.
Qed.

(* the pointer array's size as the code computes it, ((L0 << 2) & -8) + 16, for every message length *)
Definition aw_arr_w (v : Z) : word :=
  alu64 ALU_ADD (alu64 ALU_AND (alu64 ALU_SLL (Z_to_bv 64 v) (Z_to_bv 64 2)) (Z_to_bv 64 (-8))) (Z_to_bv 64 16).
Lemma aw_arr_chk : forallb (fun v => bv_unsigned (aw_arr_w v) =? SlotSpec.arr_size v) (map Z.of_nat (seq 0 8193)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma aw_arr_w_ok : forall v, 0 <= v <= 8192 -> aw_arr_w v = Z_to_bv 64 (SlotSpec.arr_size v).
Proof.
intros v Hv. pose proof (proj1 (forallb_forall _ _) aw_arr_chk v) as H.
assert (Hin : In v (map Z.of_nat (seq 0 8193))).
{ apply in_map_iff. exists (Z.to_nat v). split; [lia|]. apply in_seq. split; [apply Nat.le_0_l|].
  cbn [Nat.add]. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. change (Z.of_nat 8193) with 8193. lia. }
specialize (H Hin). apply Z.eqb_eq in H. apply bv_eq. rewrite H.
unfold SlotSpec.arr_size. rewrite unsigned_lit_small; [reflexivity|].
assert (0 <= v / 2 <= 4096) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
Qed.

(* the musl constants the strnlen wrapper reads, the frame window the stores write, the shadow base *)
Definition AWX : sv := SOff 9 0.
Definition AWspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition aw_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF LT_SB LT_SB 0) ] [] [].
Definition aw_facts5 : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF LT_SB LT_SB 0);
    (10%nat, mkAF 4096 (2^47) 0); (23%nat, mkAF 4096 (2^47) 0); (24%nat, mkAF 4096 (2^47) 0) ] [] [].
Definition aw_win (lo : Z) : YP09.region := YP09.mkRegion (Some 2%nat) 0 256 lo (lo + 8) [].
(* the registers the segment keeps: sp, gp, tp, s0, s1, s2 .. s6 and s11 *)
Definition AW_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 27]%bv.
Ltac aw_in := cbn [AW_KEEP In]; repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition aw_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma aw_E_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (aw_E regs) n = getr regs r.
Proof.
intros regs n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold aw_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
Lemma aw_preserved_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma aw_keep_pres : forall regs regs', aregs_preserved regs regs' -> forall r, In r AW_KEEP -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. cbn [AW_KEEP In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ ?rr = _ =>
      let z := eval vm_compute in (bv_unsigned rr) in
      apply (aw_preserved_reg regs regs' rr z HP); [unfold acallee_saved; lia | apply bv_eq; reflexivity] end
  | ]).
destruct Hr.
Qed.

(* the message carved from the payload holds lt_len bytes *)
Lemma aw_D_len_loc : forall cx q, x_n cx = Z.of_nat (length (x_pl cx)) -> 0 < q_r q <= x_n cx ->
  Z.of_nat (length (q_D cx q)) = lt_len (x_pl cx) (x_n cx) (q_r q).
Proof.
intros cx q Hn Hr. pose proof (lt_len_range (x_pl cx) (x_n cx) (q_r q) ltac:(lia)) as HL.
unfold q_D, lt_D, lt_rest. rewrite length_firstn, !length_skipn.
unfold SlotSpec.hdr_n in *. lia.
Qed.
(* strnlen's answer is at most the message's length, which is at most 8192 *)
Lemma aw_L0_range_loc : forall cx q, x_n cx = Z.of_nat (length (x_pl cx)) -> 0 < q_r q <= x_n cx ->
  0 <= q_L0 cx q <= lt_len (x_pl cx) (x_n cx) (q_r q) /\ lt_len (x_pl cx) (x_n cx) (q_r q) <= 8192.
Proof.
intros cx q Hn Hr. split.
- rewrite q_L0_U, <- (aw_D_len_loc cx q Hn Hr).
  pose proof (upto_len (fun b => bv_unsigned b =? 0) (q_D cx q)) as H. unfold q_U, Verbs.upto0. lia.
- unfold lt_len, SlotSpec.msg_len. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries this stretch calls: the statement's own hypotheses, word for word
   (LLVMFuzzerTestOneInput_c.v:184, :188) *)
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis ASTRNLEN : astrnlen_whole_realizesM SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen).
(* the per-binary facts, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* ---- what holds at every point of this stretch ---- *)
Definition aw_pt (cx : lcx) (q : awm) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z)
  (extra : list (Z * Z)) (rem : Z) : Prop :=
  aw_ctx0 B MT cx q ly S W regs mem md k /\ aw_msgregs cx q regs /\ aw_rec B cx q ly S W mem extra /\
  lt_bud MT cx S k acc rem.
(* the bytes those facts read: the frame below the struct words and the saved registers, the program's statics, the
   recorder's blocks *)
Definition aw_area (cx : lcx) (O : list (Z * Z)) (a : Z) : Prop :=
  (x_sp1 cx <= a < x_sp1 cx + 120) \/ (x_sp1 cx + 152 <= a < x_sp0 cx) \/ inFP cmd_PG a \/ inFP (ablocks_fp O) a.

Lemma aw_sp_loc : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem,
  aw_pt cx q ly S W regs mem md k acc extra rem ->
  spZ regs = x_sp1 cx /\ x_sp1 cx = x_sp0 cx - 256 /\ x_sp0 cx mod 16 = 0 /\
  alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47.
Proof.
intros cx q ly S W regs mem md k acc extra rem HP.
destruct HP as ((HBs & (_ & Hsp & _) & _) & _).
pose proof HBs as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HLS : LTOI_STK = 32768) by reflexivity. rewrite HLS in Hslo.
unfold x_sp1, x_sp0, LT_FRAME in *. lia.
Qed.
Lemma aw_sp16_loc : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem,
  aw_pt cx q ly S W regs mem md k acc extra rem -> spZ regs mod 16 = 0.
Proof.
intros cx q ly S W regs mem md k acc extra rem HP.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc extra rem HP) as (Hsp & E1 & Hal & _).
rewrite Hsp, E1. replace (x_sp0 cx - 256) with (x_sp0 cx + (-16) * 16) by ring. rewrite Z_mod_plus_full. exact Hal.
Qed.

Lemma aw_area_out_loc : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem a,
  aw_pt cx q ly S W regs mem md k acc extra rem -> aw_area cx (q_O1 q) a ->
  0 <= a < 2 ^ 64 /\ ~ (x_sp1 cx - 16384 <= a < x_sp1 cx) /\
  (a < alloc_ceiling \/ x_sp1 cx <= a < x_sp1 cx + 120 \/ x_sp1 cx + 152 <= a < x_sp0 cx) /\
  alloc_ceiling + 32768 - 256 <= x_sp1 cx.
Proof.
intros cx q ly S W regs mem md k acc extra rem a HP Ha.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc extra rem HP) as (Hsp & E1 & _ & Hb).
pose proof asan_consts as (C1 & _).
destruct HP as ((_ & (HJ & _) & _) & _ & HRec & _).
pose proof (proj1 HJ) as HAR.
destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia|lia| |].
- destruct Ha as (r & Hr & Hlo & Hhi). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
  cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; lia.
- destruct (inFP_ablocks_fp_inv _ a Ha) as (p & m & Hin & Hpa).
  unfold aw_rec, lt_rec in HRec. destruct HRec as (_ & _ & _ & _ & _ & Hperm).
  assert (Hin2 : In (p, m) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin. }
  destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin2) as (_ & H4096 & Hceil & _). lia.
Qed.

(* the facts of a point carried to the next one: the journal from the entry goes on, the kept registers and the
   bytes the facts read are the same, the live blocks gain [new] *)
Lemma aw_pt_move : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 acc2 new rem2,
  aw_pt cx q ly S W regs mem md k acc extra rem ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly2 S2 W2 mem2 md2 k2 ->
  (forall r, In r AW_KEEP -> getr regs2 r = getr regs r) ->
  (forall a, aw_area cx (q_O1 q) a -> rdW W2 mem2 a = rdW W mem a) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S ++ new) ->
  lt_bud MT cx S2 k2 acc2 rem2 ->
  aw_pt cx q ly2 S2 W2 regs2 mem2 md2 k2 acc2 (extra ++ new) rem2.
Proof.
intros cx q ly S W regs mem md k acc extra rem ly2 S2 W2 regs2 mem2 md2 k2 acc2 new rem2 HP HJ2 HR HK HPm Hbud.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc extra rem HP) as (_ & E1 & _ & _).
destruct HP as ((HBs & HF & HSl & R8 & R9 & R22 & Hm & Hn & Hp & Hr & Hh & Hs) & (R18 & R19 & R20 & R21 & R27) & HRec & _).
destruct HF as (HJ & Hsp & Hgp & Htp & Hsv).
assert (Hfr : forall o, 0 <= o -> o + 8 <= 120 -> forall kk, 0 <= kk < 8 ->
  rdW W2 mem2 (x_sp1 cx + o + kk) = rdW W mem (x_sp1 cx + o + kk)).
{ intros o Ho Ho8 kk Hk. apply HK. left. lia. }
unfold aw_pt. split; [|split; [|split]].
- unfold aw_ctx0. split; [exact HBs|]. split.
  { split; [exact HJ2|]. split; [unfold spZ in *; rewrite (HR 2%bv) by aw_in; exact Hsp|].
    split; [rewrite (HR 3%bv) by aw_in; exact Hgp|]. split; [rewrite (HR 4%bv) by aw_in; exact Htp|].
    intros i r0 Hi.
    assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact (Hsv i r0 Hi)|].
    intros kk Hk. apply HK. right; left. lia. }
  split.
  { intros o v Hin. rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact (HSl o v Hin)|].
    assert (Ho : 0 <= o <= 80).
    { unfold LT_SLOTS in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- _; lia|]). destruct Hin. }
    intros kk Hk. apply HK. left. lia. }
  split; [rewrite (HR 8%bv) by aw_in; exact R8|].
  split; [rewrite (HR 9%bv) by aw_in; exact R9|].
  split; [rewrite (HR 22%bv) by aw_in; exact R22|].
  split; [exact Hm|]. split; [exact Hn|]. split; [exact Hp|]. split; [exact Hr|].
  split.
  + rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact Hh|]. intros kk Hk. apply HK. left. unfold LT_HOSTB. lia.
  + rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact Hs|]. intros kk Hk. apply HK. left. unfold LT_STATEB. lia.
- unfold aw_msgregs.
  rewrite (HR 18%bv), (HR 19%bv), (HR 20%bv), (HR 21%bv), (HR 27%bv) by aw_in.
  repeat split; assumption.
- unfold aw_rec, lt_rec in *. destruct HRec as (HRp & Hspill & H2 & Hq & Hq0 & Hperm).
  split.
  { apply (rec_repA_kept B ly S (rdW W mem) ly2 S2 (rdW W2 mem2) _ _ HRp).
    - intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left.
      apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn.
    - intros a Ha. apply HK. right; right. destruct Ha as [Ha|[Ha|Ha]].
      + left. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
      + left. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
      + right. exact Ha. }
  split; [exact Hspill|]. split; [exact H2|].
  split.
  { apply (aval_mem_kept_r (rdW W mem)); [|exact Hq]. intros x Hx. apply HK. right; right; left.
    exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity|].
    change (Z.of_nat 4) with 4 in Hx. cbn [fst snd]. lia. }
  split; [exact Hq0|].
  eapply Permutation_trans; [exact HPm|]. rewrite !app_assoc. apply Permutation_app_tail.
  rewrite <- app_assoc. exact Hperm.
- exact Hbud.
Qed.

(* ---- the budget ---- *)
Lemma aw_rem_nonneg_loc : forall cx q, 0 <= aw_rem cx q.
Proof.
intros cx q. unfold aw_rem.
pose proof (EV_CHECK_ROUND_TRIP_ge0 (q_R1 cx q) (q_ws cx q)).
pose proof (ev_from_nonneg (31 - q_m q) (q_R1 cx q) (x_rest cx (lt_r' (x_pl cx) (x_n cx) (q_r q)))).
assert (0 <= EV_CHECK_REPLY /\ 0 <= EV_CHECK_ARITY /\ 0 <= EV_CHECK_WORDS /\ 0 <= EV_CHECK_REFUSAL)
  by (repeat split; apply Z.leb_le; vm_compute; reflexivity).
lia.
Qed.
Lemma aw_bud_malloc_loc : forall cx S S2 k acc rem n,
  lt_bud MT cx S k acc rem -> 1 <= rem -> 0 <= n <= 32784 -> mo_le MT S S2 (mo_malloc MT n) ->
  lt_bud MT cx S2 (k + 1) (acc + mo_malloc MT n) (rem - 1).
Proof.
intros cx S S2 k acc rem n (B1 & B2 & B3 & B4 & B5 & B6) Hr Hn Hle.
pose proof (mo_malloc_le_U MT MTL n Hn) as [M1 M2].
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_malloc MT n <= LT_U MT) by (unfold LT_U; lia).
unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 Hle)|]. split; [lia|].
set (U := LT_U MT) in *. clearbody U. nia.
Qed.

(* ---- the bytes of the message, from the payload's at the entry ---- *)
Lemma aw_msg_loc : forall cx q ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) own ly S W mem md k ->
  In (x_p cx, x_n cx) (ablocks B ly S) -> 0 < q_r q <= x_n cx ->
  aw_msg cx q (rdW W mem).
Proof.
intros cx q ly S W mem md own k HBs HJ Hin Hr.
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & Hlen & Hgarr & _).
pose proof (lt_payload_kept B MT cx ly S W mem md own k HBs HJ (fun _ => Hin)) as HK.
pose proof (lt_len_range (x_pl cx) (x_n cx) (q_r q) ltac:(lia)) as HL.
unfold aw_msg, q_src, q_D, lt_D, lt_rest.
assert (Hh : 0 < SlotSpec.hdr_n (q_r q) <= q_r q) by (unfold SlotSpec.hdr_n; lia).
intros i Hi.
rewrite length_firstn, !length_skipn in Hi.
rewrite aw_nth_firstn_loc by lia. rewrite !nth_skipn_add.
set (j := (Z.to_nat (x_n cx - q_r q) + (Z.to_nat (SlotSpec.hdr_n (q_r q)) + i))%nat).
assert (Hj : (j < length (x_pl cx))%nat) by (subst j; lia).
replace (x_p cx + (x_n cx - q_r q) + SlotSpec.hdr_n (q_r q) + Z.of_nat i) with (x_p cx + Z.of_nat j) by (subst j; lia).
rewrite (HK (Z.of_nat j)) by lia.
pose proof (garr8_mbyte SEGS _ _ _ j Hgarr ltac:(rewrite length_map; exact Hj)) as Hb.
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite (aw_nth_map_loc _ j Hj). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- the musl constants strnlen reads: read-only image bytes no one owns, kept from the entry ---- *)
Lemma aw_consts_loc : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) own ly S W mem md k ->
  consts_view SEGS 0x10358 0x10378 W mem.
Proof.
intros cx ly S W mem md own k HBs HJ a Ha.
pose proof HBs as (_ & HRO & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (cmd_snl_rom SEGS B IMG a Ha) as Hrom.
assert (Ho : ~ Exists (in_zr a) (as_owned_static B)).
{ rewrite (ts_owned B HB). intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (HF : forallb (fun r => (fst r + snd r <=? 0x10358) || (0x10378 <=? fst r)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  apply orb_true_iff in HF as [HF|HF]; apply Z.leb_le in HF; lia. }
assert (He : ~ (as_errno B <= a < as_errno B + 4)) by (rewrite (ts_errno B HB); unfold TFIB_ERRNO; lia).
assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
rewrite (F3 a Hi Ho He).
- apply HRO; [left; exact Hrom | exact Ho | exact He].
- apply fp_spares_closed.
  + apply sink_closed_pos. unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING. repeat constructor; cbn [fst]; lia.
  + intros (r & Hr & Hlo & Hhi). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; lia.
Qed.

(* ---- the strnlen wrapper in the art_post form PaArt's call step takes ---- *)
Lemma aw_snl_art_loc : forall ly S (W : world SEGS) regs mem md x n,
  ecall_pre_stk SEGS B (2 * ESTACK) ly S W regs mem md ->
  getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 < x ->
  aread_ok SEGS (2 * ESTACK) W regs mem x n ->
  consts_view SEGS 0x10358 0x10378 W mem ->
  SRr SEGS W (cfg_at SEGS (SIG CS___interceptor_trampoline_strnlen) regs mem md)
    (art_post SEGS B (2 * ESTACK) ly S W regs mem md (fun _ => False)
       (fun regs' _ => exists k, first_byte SEGS W mem x n 0 k /\ getr regs' 10 = w64 k)).
Proof.
intros ly S W regs mem md x n (HPRE & Hlo & Hscr) H10 H11 Hx (R0 & R1 & R2 & R3 & R4 & R5 & R6) HC.
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_mono.
{ apply (ASTRNLEN ly S W regs mem md x n HPRE Hlo Hscr H10 H11 R2 Hx R1).
  - intros a Ha. destruct (R3 a Ha) as [Hv Hs]. split; [exact Hv|]. unfold ascratch_stk in Hs. lia.
  - intros a Ha Hw. destruct (R3 a Ha) as [_ Hs]. exact (Hs Hw).
  - exact R4.
  - exact R5.
  - exact R6.
  - exact HC. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR & HP & Hs & HQ & Hfr & Hpres).
split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HAR|]. split; [exact HP|]. split; [exact Hs|]. split; [exact HQ|].
split; [intros a Ha Hw _; exact (Hfr a Ha Hw)|]. split; [exact Hpres|].
intros a Ha. apply Hpres. apply Hscr. exact Ha.
Qed.

(* ---- the call of the strnlen wrapper at 0x86720, from a point where aw_pt holds ---- *)
Lemma aw_strnlen_loc : forall cx q ly S (W : world SEGS) regsT memT md k acc extra rem raw Q,
  aw_pt cx q ly S W regsT memT md k acc extra rem ->
  getr regsT 10 = w64 (q_src cx q) -> getr regsT 11 = w64 (lt_len (x_pl cx) (x_n cx) (q_r q)) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     aw_pt cx q ly S W regs2 mem2 md2 k acc extra rem ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 (q_L0 cx q) ->
     SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_strnlen)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx q ly S W regsT memT md k acc extra rem raw Q HP H10 H11 H1 Hraw HK.
pose proof (aw_sp_loc cx q ly S W regsT memT md k acc extra rem HP) as (Hsp & E1 & Hal0 & Hb0).
pose proof HP as ((HBs & HF & HSl & R8 & R9 & R22 & Hm & Hnx & Hp & Hr & Hh & Hs) & HMG & HRec & Hbud).
pose proof HF as (HJ & _ & Hgp & Htp & Hsv).
pose proof HBs as (HPRE0 & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HLS : LTOI_STK = 32768) by reflexivity.
assert (HinP : In (x_p cx, x_n cx) (ablocks B ly S)).
{ unfold aw_rec, lt_rec in HRec. destruct HRec as (_ & _ & _ & _ & _ & Hperm).
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hp. }
destruct (al_blocks _ _ LAWS ly S W memT md _ _ HAR HinP) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
pose proof (lt_len_range (x_pl cx) (x_n cx) (q_r q) ltac:(lia)) as HL.
assert (Hh3 : 0 < SlotSpec.hdr_n (q_r q) <= q_r q) by (unfold SlotSpec.hdr_n; lia).
pose proof (aw_msg_loc cx q ly S W memT md [] k HBs HJ HinP Hr) as HMSG.
pose proof (aw_D_len_loc cx q Hlen Hr) as HDL.
set (len := lt_len (x_pl cx) (x_n cx) (q_r q)) in *.
assert (Hx : x_p cx <= q_src cx q) by (unfold q_src; lia).
assert (Hxn : q_src cx q + len <= x_p cx + x_n cx) by (unfold q_src; lia).
assert (Hsp' : spZ regsT = x_sp0 cx + -256) by lia.
assert (HRD : aread_ok SEGS (2 * ESTACK) W regsT memT (q_src cx q) len).
{ apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W regsT memT md (x_p cx) (x_n cx)); [exact HAR | exact HinP | lia | lia | lia |].
  rewrite Hsp, Hes. lia. }
assert (HraT : YK0s.ret_ok (getr regsT 1)) by (rewrite H1; exact Hraw).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False) (SIG CS___interceptor_trampoline_strnlen)
    W regsT memT LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S md k (-256) raw
    (fun regs' _ => exists kk, first_byte SEGS W memT (q_src cx q) len 0 kk /\ getr regs' 10 = w64 kk)
    HJ Hsp' eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HLS; lia) H1 (fun a (H : False) => False_ind _ H)).
  apply (aw_snl_art_loc ly S W regsT memT md (q_src cx q) len).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
      [] ly S W memT md k regsT (-256) HJ Hsp' eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite Hes, HLS; lia)
      HraT ltac:(rewrite Hgp; exact Hgp0) ltac:(rewrite Htp; exact Htp0)).
  - exact H10.
  - exact H11.
  - lia.
  - exact HRD.
  - exact (aw_consts_loc cx ly S W memT md [] k HBs HJ). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & HQ) & HK2).
assert (Ekk : kk = q_L0 cx q).
{ destruct Hfb as (F1 & F2 & F3). rewrite q_L0_U. unfold q_U.
  apply (aw_first_nul_loc (rdW W memT) (q_D cx q) (q_src cx q) kk HMSG); [lia | exact F2 |].
  rewrite HDL. exact F3. }
subst kk.
apply (HK regs2 mem2 md2); [|exact HP2 | exact HQ].
pose proof (aw_pt_move cx q ly S W regsT memT md k acc extra rem ly S W regs2 mem2 md2 k acc [] rem HP HJ2
  (aw_keep_pres regsT regs2 HP2)) as HM.
rewrite !app_nil_r in HM. apply HM; [|apply Permutation_refl | exact Hbud].
intros a Ha. destruct (aw_area_out_loc cx q ly S W regsT memT md k acc extra rem a HP Ha) as (Ha0 & Hout & _).
apply HK2; [exact Ha0 | rewrite Hes; lia | tauto].
Qed.

(* ---- a call of the malloc wrapper from a point where aw_pt holds; the new block joins the extra ones ---- *)
Lemma aw_malloc_loc : forall cx q ly S (W : world SEGS) regsT memT md k acc extra rem n raw Q,
  aw_pt cx q ly S W regsT memT md k acc extra rem ->
  1 <= rem -> 0 <= n <= 32784 -> bsum extra + n <= LT_WORDSB ->
  getr regsT 10 = w64 n -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     aw_pt cx q ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT n) (extra ++ [(res, n)]) (rem - 1) ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_malloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx q ly S W regsT memT md k acc extra rem n raw Q HP Hrem Hn Hsum H10 H1 Hraw Hra4 HK.
pose proof (aw_sp_loc cx q ly S W regsT memT md k acc extra rem HP) as (Hsp & E1 & Hal0 & Hb0).
pose proof HP as ((HBs & HF & HSl & R8 & R9 & R22 & Hm & Hnx & Hp & Hr & Hh & Hs) & HMG & HRec & Hbud).
pose proof HF as (HJ & _ & Hgp & Htp & Hsv).
pose proof HBs as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & Hmo & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof Hbud as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
assert (HLS : LTOI_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hsp' : spZ regsT = x_sp0 cx + -256) by lia.
pose proof (mo_malloc_le_U MT MTL n Hn) as [M1 M2].
pose proof (mo_free_nonneg MT MTL) as M3.
pose proof (LT_U_nonneg MT MTL) as HU0.
assert (HU : mo_malloc MT n <= LT_U MT) by (unfold LT_U; lia).
assert (HRU : LT_U MT <= rem * LT_U MT) by nia.
assert (MOK : mo_ok MT S (mo_malloc MT n)).
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_malloc MT n) MTL Hmo B4 M1). lia. }
assert (Hnev2 : st_nev S < EV_MAX) by lia.
assert (Hlv : blocks_bytes S + n <= LIVE_MAX).
{ pose proof (lt_rec_live B LAWS cx ly S W memT md _ _ _ extra HAR HRec) as HL.
  assert (HLL : LT_RECB + LT_WORDSB <= LIVE_LTOI) by (apply Z.leb_le; vm_compute; reflexivity).
  lia. }
assert (Hch : chain_pre ly (rdW W memT) regsT []).
{ assert (H32 : 32 < alloc_ceiling) by lia.
  apply (achain_chain_pre ly (rdW W memT) (spZ regsT) 32 [] regsT (achain_low ly (rdW W memT) (spZ regsT) 32 H32)).
  - lia.
  - unfold s0Z. rewrite R8. reflexivity.
  - unfold raZ. rewrite H1. exact Hra4. }
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ exact (amalloc04_sub SEGS B LAWS pa_segs_low MT AMALLOC4 W regsT memT LTOI_STK (x_sp0 cx) cmd_PG
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S md k n (-256) raw [] HJ H10 ltac:(unfold MALLOC_MAX; lia) Hlv
    Hsp' eq_refl ltac:(lia) ltac:(rewrite Has, HLS; lia) ltac:(rewrite Hgp; exact Hgp0) ltac:(rewrite Htp; exact Htp0)
    H1 Hraw Hnev2 Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & _ & Hr4 & Hbl & HKp & MLE & _).
destruct HKp as (K1 & K2 & K3 & _).
pose proof (proj1 HJ2) as HAR2.
assert (HND : ~ In (res, n) (ablocks B ly S)).
{ apply aw_nodup_snoc_loc. rewrite <- Hbl. exact (lt_ablocks_NoDup B LAWS ly2 S2 W2 mem2 md2 HAR2). }
assert (HFK : forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W memT a) by (intros a Ha; apply K1; lia).
apply (HK ly2 S2 W2 regs2 mem2 md2 res); [| exact HPr | exact Hres | exact HFK].
apply (aw_pt_move cx q ly S W regsT memT md k acc extra rem ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT n)
  [(res, n)] (rem - 1) HP HJ2 (aw_keep_pres regsT regs2 HPr)).
- intros a Ha. destruct (aw_area_out_loc cx q ly S W regsT memT md k acc extra rem a HP Ha) as (Ha0 & Hout & _).
  destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  + apply K1; lia.
  + apply K1; lia.
  + destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Ha) as (Hi & Ho & He). exact (K3 a Hi Ho He).
  + destruct (inFP_ablocks_fp_inv _ a Ha) as (p & m & Hin & Hpa).
    unfold aw_rec, lt_rec in HRec. destruct HRec as (_ & _ & _ & _ & _ & Hperm).
    assert (HinS : In (p, m) (ablocks B ly S)).
    { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin. }
    assert (Hne : (p, m) <> (res, n)) by (intros E; rewrite E in HinS; exact (HND HinS)).
    pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p m res n HAR2
      ltac:(rewrite Hbl; apply in_or_app; left; exact HinS)
      ltac:(rewrite Hbl; apply in_or_app; right; left; reflexivity) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    replace a with (p + (a - p)) by lia.
    apply (K2 p m (a - p) HinS); [lia|]. cbv beta. lia.
- rewrite Hbl. apply Permutation_refl.
- exact (aw_bud_malloc_loc cx S S2 k acc rem n Hbud Hrem Hn MLE).
Qed.

(* ---- the bytes a stretch of the walk leaves as they were: all but its one write window ---- *)
Lemma aw_win_kept_loc : forall E (W : world SEGS) (m m' : word -> option byte) lo sp,
  frame_of E [aw_win lo] (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> bv_unsigned (ew E 2) = sp ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp + lo <= a < sp + lo + 8) -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' lo sp HF Hsp a Ha Hn.
apply (kept_of_frame (segs:=SEGS) E [aw_win lo] (w_H W) m m' (fun a => sp + lo <= a < sp + lo + 8) HF); [|exact Ha|exact Hn].
intros b wlo whi a' Hin Hr. cbn [windows aw_win map In] in Hin. destruct Hin as [Hq|[]].
injection Hq as <- <- <-. cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
Lemma aw_nowin_kept_loc : forall E (W : world SEGS) (m m' : word -> option byte),
  frame_of E [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' HF a Ha.
apply (kept_of_frame (segs:=SEGS) E [] (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin. cbn [windows map In] in Hin. destruct Hin.
Qed.

(* ---- the symbolic seeds of the stretches: every register its own atom, s1 the shadow base, at most one write
   window in the frame and no chunk (libreac/fuzz_grant's fast form of symbolic runs over shadow stores) ---- *)
Lemma aw_facts_ok_loc : forall regs, 2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> getr regs 9 = w64 LT_SB ->
  facts_ok (aw_E regs) aw_facts.
Proof.
intros regs Hs Ha H9. split; [|split; [exact I | exact I]].
cbn [aw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (aw_E_reg regs 2 2%bv eq_refl), (aw_E_reg regs 9 9%bv eq_refl), H9. fold (spZ regs).
unfold w64, LT_SB. rewrite unsigned_lit_small by lia.
change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
Lemma aw_facts5_ok_loc : forall regs t c r, 2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 9 = w64 LT_SB -> getr regs 10 = w64 r -> getr regs 23 = w64 c -> getr regs 24 = w64 t ->
  4096 <= r <= 2 ^ 47 -> 4096 <= c <= 2 ^ 47 -> 4096 <= t <= 2 ^ 47 ->
  facts_ok (aw_E regs) aw_facts5.
Proof.
intros regs t c r Hs Ha H9 H10 H23 H24 Hr Hc Ht. split; [|split; [exact I | exact I]].
cbn [aw_facts5 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (aw_E_reg regs 2 2%bv eq_refl), (aw_E_reg regs 9 9%bv eq_refl), (aw_E_reg regs 10 10%bv eq_refl),
  (aw_E_reg regs 23 23%bv eq_refl), (aw_E_reg regs 24 24%bv eq_refl), H9, H10, H23, H24. fold (spZ regs).
unfold w64, LT_SB. rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
Lemma aw_win_ok_loc : forall (W : world SEGS) regs mem lo, 0 <= lo -> lo + 8 <= 256 ->
  (forall a, spZ regs <= a < spZ regs + 256 -> apresent (w_H W) mem a) -> spZ regs + 256 <= 2 ^ 64 ->
  region_ok SEGS (aw_E regs) (mrestrict (w_H W) mem) (aw_win lo).
Proof.
intros W regs mem lo H0 H8 Hpres Hhi. unfold region_ok, aw_win.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (aw_E_reg regs 2 2%bv eq_refl). fold (spZ regs).
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R. fold (spZ regs) in R.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.
Lemma aw_seed0_loc : forall pc (W : world SEGS) regs mem,
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> getr regs 9 = w64 LT_SB ->
  st_ok_pi SEGS VAL (aw_E regs) (mkSS pc sr_atoms [] None aw_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem Hs Ha H9. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold aw_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- exact (aw_facts_ok_loc regs Hs Ha H9).
Qed.
Lemma aw_seed1_loc : forall pc lo G (W : world SEGS) regs mem,
  regions_wf [aw_win lo] = true -> 0 <= lo -> lo + 8 <= 256 ->
  (forall a, spZ regs <= a < spZ regs + 256 -> apresent (w_H W) mem a) -> spZ regs + 256 <= 2 ^ 64 ->
  facts_ok (aw_E regs) G ->
  st_ok_pi SEGS VAL (aw_E regs) (mkSS pc sr_atoms [aw_win lo] None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc lo G W regs mem Hwf H0 H8 Hpres Hhi HG. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold aw_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil]. exact (aw_win_ok_loc W regs mem lo H0 H8 Hpres Hhi).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- exact HG.
Qed.
(* the frame below the entry sp is present at every point *)
Lemma aw_pres_loc : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem,
  aw_pt cx q ly S W regs mem md k acc extra rem ->
  forall a, spZ regs <= a < spZ regs + 256 -> apresent (w_H W) mem a.
Proof.
intros cx q ly S W regs mem md k acc extra rem HP a Ha.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc extra rem HP) as (Hsp & E1 & _).
destruct HP as ((_ & (HJ & _) & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
apply Hpres. assert (HLS : LTOI_STK = 32768) by reflexivity. lia.
Qed.
(* a frame window of the walk is in the function's own stack window *)
Lemma aw_awr_loc : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem lo E,
  aw_pt cx q ly S W regs mem md k acc extra rem -> bv_unsigned (ew E 2) = spZ regs -> 0 <= lo -> lo + 8 <= 256 ->
  awr_ok SEGS B E [aw_win lo] LTOI_STK (x_sp0 cx) cmd_PG (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S)
    (frames (x_S cx)) ly [].
Proof.
intros cx q ly S W regs mem md k acc extra rem lo E HP Hew H0 H8 a (r & Hin & Ha).
pose proof (aw_sp_loc cx q ly S W regs mem md k acc extra rem HP) as (Hsp & E1 & _ & Hb).
destruct Hin as [<- | []]. cbn [aw_win YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Hew in Ha.
left. assert (HLS : LTOI_STK = 32768) by reflexivity. lia.
Qed.
(* the blocks the stretch made are in the heap *)
Lemma aw_extra_blk_loc : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem p n,
  aw_pt cx q ly S W regs mem md k acc extra rem -> In (p, n) extra ->
  4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof.
intros cx q ly S W regs mem md k acc extra rem p n HP Hin.
destruct HP as ((_ & (HJ & _) & _) & _ & HRec & _).
unfold aw_rec, lt_rec in HRec. destruct HRec as (_ & _ & _ & _ & _ & Hperm).
assert (Hin2 : In (p, n) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. right. exact Hin. }
destruct (al_blocks _ _ LAWS ly S W mem md p n (proj1 HJ) Hin2) as (_ & H4096 & Hceil & _). lia.
Qed.
Lemma aw_payload_blk_loc : forall cx q ly S (W : world SEGS) regs mem md k acc extra rem,
  aw_pt cx q ly S W regs mem md k acc extra rem -> In (x_p cx, x_n cx) (ablocks B ly S).
Proof.
intros cx q ly S W regs mem md k acc extra rem HP.
destruct HP as ((_ & _ & _ & _ & _ & _ & _ & _ & Hp & _) & _ & HRec & _).
unfold aw_rec, lt_rec in HRec. destruct HRec as (_ & _ & _ & _ & _ & Hperm).
apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hp.
Qed.

(* the kept registers after a run: each is still its own atom *)
Ltac aw_keep_run HS EEo :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [AW_KEEP In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in
      lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]);
  destruct Hr.

(* ---- 0x86718: a0 := s4 (the message), a1 := s3 (its length), jal strnlen ---- *)
Lemma aw_st1 : forall cx q ly S (W : world SEGS) regs mem md k acc,
  aw_pt cx q ly S W regs mem md k acc [] (aw_rem cx q + 3) ->
  (forall regs2 mem2 md2,
     aw_pt cx q ly S W regs2 mem2 md2 k acc [] (aw_rem cx q + 3) -> getr regs2 10 = w64 (q_L0 cx q) ->
     SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x240)) mem2 (seg_rom SEGS)) md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_SMRA)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx q ly S W regs mem md k acc HP HK.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc [] (aw_rem cx q + 3) HP) as (Hsp & E1 & Hal0 & Hb0).
pose proof HP as ((HBs & (HJ & _) & _ & _ & R9 & _) & (_ & R19 & R20 & _) & _ & Hbud).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (aw_seed0_loc 0x234 W regs mem ltac:(lia) (aw_sp16_loc _ _ _ _ _ _ _ _ _ _ _ _ HP) R9) as HS.
assert (SHOK : sh_ok SEGS AWX [] (aw_E regs) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (aw_E regs)) by (unfold aw_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (aw_E regs) n = getr regs rr)
  by (intros n rr Hn; exact (aw_E_reg regs n rr Hn)).
remember (aw_E regs) as E eqn:HE. clear HE.
unfold LO_SMRA.
paj_run_tok RUN HS HJ SHOK AWspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HKR : forall r, In r AW_KEEP -> getr (ms_regs ms) r = getr regs r) by aw_keep_run HS EEo.
assert (KEEP : forall a, aw_area cx (q_O1 q) a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. destruct (aw_area_out_loc cx q ly S W regs mem md k acc [] _ a HP Ha) as (Ha0 & _).
  exact (aw_nowin_kept_loc E W mem (ms_mem ms) HFr a Ha0). }
pose proof (aw_pt_move cx q ly S W regs mem md k acc [] (aw_rem cx q + 3) ly S W (ms_regs ms) (ms_mem ms) md1 k acc []
  (aw_rem cx q + 3) HP HJ HKR KEEP ltac:(rewrite app_nil_r; apply Permutation_refl) Hbud) as HPT.
cbn [app] in HPT.
eapply (aw_strnlen_loc cx q ly S W (ms_regs ms) (ms_mem ms) md1 k acc [] (aw_rem cx q + 3) _ _ HPT).
- rewrite P10, (EEo 20%nat 20%bv eq_refl). exact R20.
- rewrite P11, (EEo 19%nat 19%bv eq_refl). exact R19.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros regs2 mem2 md2 HP2 _ H10. exact (HK regs2 mem2 md2 HP2 H10).
Qed.

(* ---- 0x86724: s10 := L0, s7 := L0 + 1, a0 := s7, jal malloc (text) ---- *)
Lemma aw_st2 : forall cx q ly S (W : world SEGS) regs mem md k acc,
  aw_pt cx q ly S W regs mem md k acc [] (aw_rem cx q + 3) -> getr regs 10 = w64 (q_L0 cx q) ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 text,
     aw_pt cx q ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (q_L0 cx q + 1)) [(text, q_L0 cx q + 1)]
       (aw_rem cx q + 2) ->
     getr regs2 26 = w64 (q_L0 cx q) -> getr regs2 23 = w64 (q_L0 cx q + 1) -> getr regs2 10 = w64 text ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x250)) mem2 (seg_rom SEGS)) md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x240)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx q ly S W regs mem md k acc HP H10 HK.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc [] (aw_rem cx q + 3) HP) as (Hsp & E1 & Hal0 & Hb0).
pose proof HP as ((HBs & (HJ & _) & _ & _ & R9 & _ & _ & _ & _ & Hr & _) & _ & _ & Hbud).
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof (aw_L0_range_loc cx q Hlen Hr) as (HL0 & HL8).
pose proof (aw_rem_nonneg_loc cx q) as Hrem.
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (aw_seed0_loc 0x240 W regs mem ltac:(lia) (aw_sp16_loc _ _ _ _ _ _ _ _ _ _ _ _ HP) R9) as HS.
assert (SHOK : sh_ok SEGS AWX [] (aw_E regs) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (aw_E regs)) by (unfold aw_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (aw_E regs) n = getr regs rr)
  by (intros n rr Hn; exact (aw_E_reg regs n rr Hn)).
remember (aw_E regs) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK AWspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (23%bv : bv 5) P23. prreg HS (26%bv : bv 5) P26.
assert (HKR : forall r, In r AW_KEEP -> getr (ms_regs ms) r = getr regs r) by aw_keep_run HS EEo.
assert (KEEP : forall a, aw_area cx (q_O1 q) a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. destruct (aw_area_out_loc cx q ly S W regs mem md k acc [] _ a HP Ha) as (Ha0 & _).
  exact (aw_nowin_kept_loc E W mem (ms_mem ms) HFr a Ha0). }
pose proof (aw_pt_move cx q ly S W regs mem md k acc [] (aw_rem cx q + 3) ly S W (ms_regs ms) (ms_mem ms) md1 k acc []
  (aw_rem cx q + 3) HP HJ HKR KEEP ltac:(rewrite app_nil_r; apply Permutation_refl) Hbud) as HPT.
cbn [app] in HPT.
rewrite (EEo 10%nat 10%bv eq_refl), H10 in P10, P23, P26.
unfold w64 in P10, P23. rewrite unsigned_lit_small in P10, P23 by lia.
eapply (aw_malloc_loc cx q ly S W (ms_regs ms) (ms_mem ms) md1 k acc [] (aw_rem cx q + 3) (q_L0 cx q + 1) _ _ HPT).
- lia.
- lia.
- cbn [bsum]. unfold LT_WORDSB. lia.
- exact P10.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 res HP2 HPr Hres _. cbn [app] in HP2.
  replace (aw_rem cx q + 3 - 1) with (aw_rem cx q + 2) in HP2 by ring.
  apply (HK ly2 S2 W2 regs2 mem2 md2 res HP2).
  + rewrite (aw_preserved_reg _ _ 26%bv 26 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    exact P26.
  + rewrite (aw_preserved_reg _ _ 23%bv 23 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    exact P23.
  + exact Hres.
Qed.

(* ---- 0x86734: s8 := text, sd text,120(sp), a0 := s7, jal malloc (copy) ---- *)
Lemma aw_st3 : forall cx q ly S (W : world SEGS) regs mem md k acc text,
  aw_pt cx q ly S W regs mem md k acc [(text, q_L0 cx q + 1)] (aw_rem cx q + 2) ->
  getr regs 26 = w64 (q_L0 cx q) -> getr regs 23 = w64 (q_L0 cx q + 1) -> getr regs 10 = w64 text ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 copy,
     aw_pt cx q ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (q_L0 cx q + 1))
       [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1)] (aw_rem cx q + 1) ->
     getr regs2 26 = w64 (q_L0 cx q) -> getr regs2 24 = w64 text -> getr regs2 10 = w64 copy ->
     rdword (rdW W2 mem2) (x_sp1 cx + LT_W) = Some text ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x260)) mem2 (seg_rom SEGS)) md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x250)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx q ly S W regs mem md k acc text HP H26 H23 H10 HK.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc _ _ HP) as (Hsp & E1 & Hal0 & Hb0).
pose proof HP as ((HBs & (HJ & _) & _ & _ & R9 & _ & _ & _ & _ & Hr & _) & _ & _ & Hbud).
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof (aw_L0_range_loc cx q Hlen Hr) as (HL0 & HL8).
pose proof (aw_rem_nonneg_loc cx q) as Hrem.
pose proof (aw_extra_blk_loc cx q ly S W regs mem md k acc _ _ text _ HP (or_introl eq_refl)) as (Ht4 & Htc).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hrq1 _].
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (aw_seed1_loc 0x250 120 aw_facts W regs mem eq_refl ltac:(lia) ltac:(lia)
  (aw_pres_loc cx q ly S W regs mem md k acc _ _ HP) ltac:(lia)
  (aw_facts_ok_loc regs ltac:(lia) (aw_sp16_loc _ _ _ _ _ _ _ _ _ _ _ _ HP) R9)) as HS.
assert (SHOK : sh_ok SEGS AWX [] (aw_E regs) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (aw_E regs)) by (unfold aw_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (aw_E regs) n = getr regs rr)
  by (intros n rr Hn; exact (aw_E_reg regs n rr Hn)).
assert (Usp : bv_unsigned (ew (aw_E regs) 2) = spZ regs) by (rewrite (aw_E_reg regs 2 2%bv eq_refl); reflexivity).
remember (aw_E regs) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK AWspan.
{ exact (aw_awr_loc cx q ly S W regs mem md k acc _ _ 120 E HP Usp ltac:(lia) ltac:(lia)). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
assert (HKR : forall r, In r AW_KEEP -> getr (ms_regs ms) r = getr regs r) by aw_keep_run HS EEo.
assert (KEEP : forall a, aw_area cx (q_O1 q) a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. destruct (aw_area_out_loc cx q ly S W regs mem md k acc _ _ a HP Ha) as (Ha0 & _ & Hlow & Hac).
  apply (aw_win_kept_loc E W mem (ms_mem ms) 120 (spZ regs) HFr Usp a Ha0). lia. }
pose proof (aw_pt_move cx q ly S W regs mem md k acc _ _ ly S W (ms_regs ms) (ms_mem ms) md1 k acc []
  (aw_rem cx q + 2) HP HJ HKR KEEP ltac:(rewrite app_nil_r; apply Permutation_refl) Hbud) as HPT.
cbn [app] in HPT.
assert (HW0 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + 120) = Some text).
{ apply PaLibF.rdword_of_val_mem; [|lia].
  rewrite <- Hsp.
  refine (YI67.st_chunk_val SEGS E _ _ 0 (YP09.mkRegion (Some 2%nat) 0 256 120 128 [YP09.mkChunk 120 (CVal 8 (SOff 10 0))])
    2%nat 120 8 (SOff 10 0) (spZ regs) text HS eq_refl eq_refl (or_introl eq_refl) Usp _ _ _).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl), H10. reflexivity.
  - change (8 * Z.of_N 8) with 64. lia.
  - change (Z.of_N 8) with 8. lia. }
rewrite (EEo 23%nat 23%bv eq_refl), H23 in P10. rewrite (EEo 10%nat 10%bv eq_refl), H10 in P24.
rewrite (EEo 26%nat 26%bv eq_refl), H26 in P26.
eapply (aw_malloc_loc cx q ly S W (ms_regs ms) (ms_mem ms) md1 k acc _ (aw_rem cx q + 2) (q_L0 cx q + 1) _ _ HPT).
- lia.
- lia.
- cbn [bsum fst snd]. unfold LT_WORDSB. lia.
- exact P10.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 res HP2 HPr Hres HFK. cbn [app] in HP2.
  replace (aw_rem cx q + 2 - 1) with (aw_rem cx q + 1) in HP2 by ring.
  apply (HK ly2 S2 W2 regs2 mem2 md2 res HP2).
  + rewrite (aw_preserved_reg _ _ 26%bv 26 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    exact P26.
  + rewrite (aw_preserved_reg _ _ 24%bv 24 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    exact P24.
  + exact Hres.
  + rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W2 mem2)); [unfold LT_W; exact HW0|].
    intros kk Hk. apply HFK. unfold LT_W. lia.
Qed.

(* ---- 0x86744: s7 := copy, sd copy,128(sp), a0 := ((s10 << 2) & -8) + 16, jal malloc (the array) ---- *)
Lemma aw_st4 : forall cx q ly S (W : world SEGS) regs mem md k acc text copy,
  aw_pt cx q ly S W regs mem md k acc [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1)] (aw_rem cx q + 1) ->
  getr regs 26 = w64 (q_L0 cx q) -> getr regs 24 = w64 text -> getr regs 10 = w64 copy ->
  rdword (rdW W mem) (x_sp1 cx + LT_W) = Some text ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 arr,
     aw_pt cx q ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (SlotSpec.arr_size (q_L0 cx q)))
       [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))] (aw_rem cx q) ->
     getr regs2 26 = w64 (q_L0 cx q) -> getr regs2 24 = w64 text -> getr regs2 23 = w64 copy ->
     getr regs2 10 = w64 arr ->
     rdword (rdW W2 mem2) (x_sp1 cx + LT_W) = Some text -> rdword (rdW W2 mem2) (x_sp1 cx + LT_W + 8) = Some copy ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x278)) mem2 (seg_rom SEGS)) md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x260)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx q ly S W regs mem md k acc text copy HP H26 H24 H10 HWt HK.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc _ _ HP) as (Hsp & E1 & Hal0 & Hb0).
pose proof HP as ((HBs & (HJ & _) & _ & _ & R9 & _ & _ & _ & _ & Hr & _) & _ & _ & Hbud).
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof (aw_L0_range_loc cx q Hlen Hr) as (HL0 & HL8).
pose proof (aw_rem_nonneg_loc cx q) as Hrem.
pose proof (aw_extra_blk_loc cx q ly S W regs mem md k acc _ _ copy _ HP (or_intror (or_introl eq_refl))) as (Hc4 & Hcc).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hrq1 _].
assert (HA : 16 <= SlotSpec.arr_size (q_L0 cx q) <= 32784).
{ unfold SlotSpec.arr_size. assert (0 <= q_L0 cx q / 2 <= 4096) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  lia. }
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (aw_seed1_loc 0x260 128 aw_facts W regs mem eq_refl ltac:(lia) ltac:(lia)
  (aw_pres_loc cx q ly S W regs mem md k acc _ _ HP) ltac:(lia)
  (aw_facts_ok_loc regs ltac:(lia) (aw_sp16_loc _ _ _ _ _ _ _ _ _ _ _ _ HP) R9)) as HS.
assert (SHOK : sh_ok SEGS AWX [] (aw_E regs) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (aw_E regs)) by (unfold aw_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (aw_E regs) n = getr regs rr)
  by (intros n rr Hn; exact (aw_E_reg regs n rr Hn)).
assert (Usp : bv_unsigned (ew (aw_E regs) 2) = spZ regs) by (rewrite (aw_E_reg regs 2 2%bv eq_refl); reflexivity).
remember (aw_E regs) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK AWspan.
{ exact (aw_awr_loc cx q ly S W regs mem md k acc _ _ 128 E HP Usp ltac:(lia) ltac:(lia)). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (26%bv : bv 5) P26.
assert (HKR : forall r, In r AW_KEEP -> getr (ms_regs ms) r = getr regs r) by aw_keep_run HS EEo.
assert (KEEP : forall a, aw_area cx (q_O1 q) a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. destruct (aw_area_out_loc cx q ly S W regs mem md k acc _ _ a HP Ha) as (Ha0 & _ & Hlow & Hac).
  apply (aw_win_kept_loc E W mem (ms_mem ms) 128 (spZ regs) HFr Usp a Ha0). lia. }
pose proof (aw_pt_move cx q ly S W regs mem md k acc _ _ ly S W (ms_regs ms) (ms_mem ms) md1 k acc []
  (aw_rem cx q + 1) HP HJ HKR KEEP ltac:(rewrite app_nil_r; apply Permutation_refl) Hbud) as HPT.
cbn [app] in HPT.
assert (HW0 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + 120) = Some text).
{ rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [unfold LT_W in HWt; exact HWt|].
  intros kk Hk. apply (aw_win_kept_loc E W mem (ms_mem ms) 128 (spZ regs) HFr Usp); lia. }
assert (HW8 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + 128) = Some copy).
{ apply PaLibF.rdword_of_val_mem; [|lia].
  rewrite <- Hsp.
  refine (YI67.st_chunk_val SEGS E _ _ 0 (YP09.mkRegion (Some 2%nat) 0 256 128 136 [YP09.mkChunk 128 (CVal 8 (SOff 10 0))])
    2%nat 128 8 (SOff 10 0) (spZ regs) copy HS eq_refl eq_refl (or_introl eq_refl) Usp _ _ _).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl), H10. reflexivity.
  - change (8 * Z.of_N 8) with 64. lia.
  - change (Z.of_N 8) with 8. lia. }
assert (P10' : getr (ms_regs ms) 10 = w64 (SlotSpec.arr_size (q_L0 cx q))).
{ rewrite P10, (EEo 26%nat 26%bv eq_refl), H26. exact (aw_arr_w_ok (q_L0 cx q) ltac:(lia)). }
rewrite (EEo 10%nat 10%bv eq_refl), H10 in P23. rewrite (EEo 24%nat 24%bv eq_refl), H24 in P24.
rewrite (EEo 26%nat 26%bv eq_refl), H26 in P26.
eapply (aw_malloc_loc cx q ly S W (ms_regs ms) (ms_mem ms) md1 k acc _ (aw_rem cx q + 1) (SlotSpec.arr_size (q_L0 cx q))
  _ _ HPT).
- lia.
- lia.
- cbn [bsum fst snd]. unfold LT_WORDSB. lia.
- exact P10'.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 res HP2 HPr Hres HFK. cbn [app] in HP2.
  replace (aw_rem cx q + 1 - 1) with (aw_rem cx q) in HP2 by ring.
  apply (HK ly2 S2 W2 regs2 mem2 md2 res HP2).
  + rewrite (aw_preserved_reg _ _ 26%bv 26 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    exact P26.
  + rewrite (aw_preserved_reg _ _ 24%bv 24 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    exact P24.
  + rewrite (aw_preserved_reg _ _ 23%bv 23 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    exact P23.
  + exact Hres.
  + rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W2 mem2)); [unfold LT_W; exact HW0|].
    intros kk Hk. apply HFK. unfold LT_W. lia.
  + rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W2 mem2));
      [unfold LT_W; replace (x_sp1 cx + 120 + 8) with (x_sp1 cx + 128) by lia; exact HW8|].
    intros kk Hk. apply HFK. unfold LT_W. lia.
Qed.

(* ---- 0x8675c: sd arr,136(sp), the three NULL tests (refuted: every block is at or above 4096), s9 := arr, then
   0x86770 = AW_M ---- *)
Lemma aw_st5 : forall m, AW_M_stmt B MT m ->
  forall cx q ly S (W : world SEGS) regs mem md k acc text copy arr, q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_pt cx q ly S W regs mem md k acc
    [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))] (aw_rem cx q) ->
  getr regs 26 = w64 (q_L0 cx q) -> getr regs 24 = w64 text -> getr regs 23 = w64 copy -> getr regs 10 = w64 arr ->
  rdword (rdW W mem) (x_sp1 cx + LT_W) = Some text -> rdword (rdW W mem) (x_sp1 cx + LT_W + 8) = Some copy ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x278)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros m HM cx q ly S W regs mem md k acc text copy arr Hm HFRM HP H26 H24 H23 H10 HWt HWc.
pose proof (aw_sp_loc cx q ly S W regs mem md k acc _ _ HP) as (Hsp & E1 & Hal0 & Hb0).
pose proof HP as ((HBs & (HJ & _) & _ & _ & R9 & _ & _ & _ & _ & Hr & _) & _ & _ & Hbud).
pose proof (aw_extra_blk_loc cx q ly S W regs mem md k acc _ _ text _ HP (or_introl eq_refl)) as (Ht4 & Htc).
pose proof (aw_extra_blk_loc cx q ly S W regs mem md k acc _ _ copy _ HP (or_intror (or_introl eq_refl))) as (Hc4 & Hcc).
pose proof (aw_extra_blk_loc cx q ly S W regs mem md k acc _ _ arr _ HP (or_intror (or_intror (or_introl eq_refl))))
  as (Ha4 & Hac').
pose proof (aw_payload_blk_loc cx q ly S W regs mem md k acc _ _ HP) as HinP.
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof (aw_L0_range_loc cx q Hlen Hr) as (HL0 & HL8).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hrq1 _].
pose proof (req_size_pos (SlotSpec.arr_size (q_L0 cx q))
  ltac:(unfold SlotSpec.arr_size; pose proof (Z.div_pos (q_L0 cx q) 2 ltac:(lia) ltac:(lia)); lia))
  as [Hrq2 _].
pose proof asan_consts as (C1 & _).
pose proof (aw_seed1_loc 0x278 136 aw_facts5 W regs mem eq_refl ltac:(lia) ltac:(lia)
  (aw_pres_loc cx q ly S W regs mem md k acc _ _ HP) ltac:(lia)
  (aw_facts5_ok_loc regs text copy arr ltac:(lia) (aw_sp16_loc _ _ _ _ _ _ _ _ _ _ _ _ HP) R9 H10 H23 H24
    ltac:(lia) ltac:(lia) ltac:(lia))) as HS.
assert (SHOK : sh_ok SEGS AWX [] (aw_E regs) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (aw_E regs)) by (unfold aw_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (aw_E regs) n = getr regs rr)
  by (intros n rr Hn; exact (aw_E_reg regs n rr Hn)).
assert (Usp : bv_unsigned (ew (aw_E regs) 2) = spZ regs) by (rewrite (aw_E_reg regs 2 2%bv eq_refl); reflexivity).
remember (aw_E regs) as E eqn:HE. clear HE.
paj_run_to_tok RUNTO HS HJ SHOK AWspan 0x28c.
{ exact (aw_awr_loc cx q ly S W regs mem md k acc _ _ 136 E HP Usp ltac:(lia) ltac:(lia)). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (10%bv : bv 5) P10. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26.
assert (HKR : forall r, In r AW_KEEP -> getr (ms_regs ms) r = getr regs r) by aw_keep_run HS EEo.
assert (KEEP : forall a, aw_area cx (q_O1 q) a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. destruct (aw_area_out_loc cx q ly S W regs mem md k acc _ _ a HP Ha) as (Ha0 & _ & Hlow & Hac).
  apply (aw_win_kept_loc E W mem (ms_mem ms) 136 (spZ regs) HFr Usp a Ha0). lia. }
pose proof (aw_pt_move cx q ly S W regs mem md k acc _ _ ly S W (ms_regs ms) (ms_mem ms) md1 k acc []
  (aw_rem cx q) HP HJ HKR KEEP ltac:(rewrite app_nil_r; apply Permutation_refl) Hbud) as HPT.
cbn [app] in HPT.
assert (HW0 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_W) = Some text).
{ rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact HWt|].
  intros kk Hk. apply (aw_win_kept_loc E W mem (ms_mem ms) 136 (spZ regs) HFr Usp); unfold LT_W; lia. }
assert (HW8 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_W + 8) = Some copy).
{ rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact HWc|].
  intros kk Hk. apply (aw_win_kept_loc E W mem (ms_mem ms) 136 (spZ regs) HFr Usp); unfold LT_W; lia. }
assert (HW16 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_W + 16) = Some arr).
{ apply PaLibF.rdword_of_val_mem; [|lia].
  unfold LT_W. replace (x_sp1 cx + 120 + 16) with (spZ regs + 136) by lia.
  pose proof HS as HS'. unfold st_ok_pi in HS'.
  refine (YI67.st_chunk_val SEGS E _ _ 0 (YP09.mkRegion (Some 2%nat) 0 256 136 144 [YP09.mkChunk 136 (CVal 8 (SOff 10 0))])
    2%nat 136 8 (SOff 10 0) (spZ regs) arr HS' eq_refl eq_refl (or_introl eq_refl) Usp _ _ _).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl), H10. reflexivity.
  - change (8 * Z.of_N 8) with 64. lia.
  - change (Z.of_N 8) with 8. lia. }
pose proof (aw_msg_loc cx q ly S W (ms_mem ms) md1 [] k HBs HJ HinP Hr) as HMSG.
destruct HPT as (HC0 & HMG & HRec & Hbud').
exact (HM cx q ly S W (ms_regs ms) (ms_mem ms) md1 k acc text copy arr Hm HFRM (conj HC0 Hbud') HMG
  ltac:(rewrite aw_blocks_eq; exact HRec) HMSG (conj HW0 (conj HW8 HW16))
  ltac:(rewrite P24, (EEo 24%nat 24%bv eq_refl); exact H24) ltac:(rewrite P23, (EEo 23%nat 23%bv eq_refl); exact H23)
  ltac:(rewrite P25, (EEo 10%nat 10%bv eq_refl); exact H10) ltac:(rewrite P10, (EEo 10%nat 10%bv eq_refl); exact H10)
  ltac:(rewrite P26, (EEo 26%nat 26%bv eq_refl); exact H26)).
Qed.

(* ---- the segment: from 0x86718 (LT_W_stmt's point, in this file's words) to 0x86770 (AW_M) ---- *)
Lemma aw_seg_M : forall m, AW_M_stmt B MT m -> AW_W_stmt B MT m.
Proof.
intros m HM cx q ly S W regs mem md k acc Hm HFRM HC0 HMG HRec Hbud.
assert (HP : aw_pt cx q ly S W regs mem md k acc [] (aw_rem cx q + 3)) by (split; [exact HC0 | split; [exact HMG | split; [exact HRec | exact Hbud]]]).
apply (aw_st1 cx q ly S W regs mem md k acc HP).
intros regs1 mem1 md1 HP1 H10.
apply (aw_st2 cx q ly S W regs1 mem1 md1 k acc HP1 H10).
intros ly2 S2 W2 regs2 mem2 md2 text HP2 H26 H23 H10b.
apply (aw_st3 cx q ly2 S2 W2 regs2 mem2 md2 _ _ text HP2 H26 H23 H10b).
intros ly3 S3 W3 regs3 mem3 md3 copy HP3 H26c H24c H10c HW3.
apply (aw_st4 cx q ly3 S3 W3 regs3 mem3 md3 _ _ text copy HP3 H26c H24c H10c HW3).
intros ly4 S4 W4 regs4 mem4 md4 arr HP4 H26d H24d H23d H10d HW4a HW4b.
exact (aw_st5 m HM cx q ly4 S4 W4 regs4 mem4 md4 _ _ text copy arr Hm HFRM HP4 H26d H24d H23d H10d HW4a HW4b).
Qed.

End e.
End f.
End d.
