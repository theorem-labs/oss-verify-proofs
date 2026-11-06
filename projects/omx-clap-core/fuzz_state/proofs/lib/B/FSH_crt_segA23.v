(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its addresses and numbers changed; 2709 of its 2837 lines of code are new or changed and 1228 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSH_crt_segA.v; 2166 of its 2393 lines of code are new or changed and 2610 lines of the source are left out. *)
(* rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   15f6f0ad6e5 lib/A/FSH_crt_segA23.v)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - RT : CrtRt B
   (not FsRt), and the unused a23_ss54 (B 0x82094) deleted (a working branch 1ab57ca7ad7).
   Port source: a working branch 15f6f0ad6e5 proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA23.v (2582
   lines, on A base v32 a working branch 9ffe6bce6eb: its FSH_crt_base / site / cstr / FSW_crt_tbl blobs are
   v32's), whose own rule-24 line is: PORTED from a working branch d25a984c903
   proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd2.v (sd2_tail :494-870, sd2_postlen :458-489, sd2_last
   :312-407, the canonical / non-canonical split :732-869 with B64Canon.canonical_enc the same bridge),
   check_round_trip_stdefs.v St2 :244 / St3 :260 and check_round_trip_loops.v crt_canonical :1032. The donor is a
   concrete-execution proof and is not importable; only the argument is ported.
   Same Lemma names and statement shapes as the A file, over image B (lib/B/YB1v.v tfibsegs, fs.asan-ubsan), on the B
   interface lib/B/FSH_crt_base.v (B base v32, a working branch 985265b6291), lib/B/FSH_crt_site.v,
   lib/B/FSH_crt_cstr.v and lib/B/FSW_crt_tbl.v. Base v33 (K / CNT / LIVE_82268 by trace) is not needed: this file
   reads only K_82068 / CNT_82068 / LIVE_82068 (through crt_keepA and crt_INV_82068), which v33 leaves unchanged.
   A new file: no licence lines (internal).

   check_round_trip (fs.asan-ubsan 0x81b9c, 693 insns; A: fs.asan 0x81a9c), build B, lane A23: the two straight-line
   pieces between the walk's two loops -
     segment 6  B 0x820a4 -> 0x8210c (crt_INV_81f58 -> crt_INV_81fb8; A 0x81f58 -> 0x81fb8): the NUL store
       `sb zero, 0(a0)` at 0x820b4 with its ASan shadow check (slow path 0x82624 -> 0x820b4), the text's `beqz` at
       0x820bc, the strlen thunk at 0x820c0 (FsRt.fr_strlen through PC_strlen 0x426c4), the length guard
       `bne a0, s11` at 0x820c4, and the frame-object registers / slot stores / loop-7 constants 0x820c8 .. 0x82108;
     segments 8-9  B 0x82180 -> 0x821c4 (crt_INV_82028 -> crt_INV_82068; A 0x82028 -> 0x82068): the UBSan
       pointer-overflow test `bltu a2, a1` at 0x82180 (B only), the NUL store at 0x8219c with its shadow check (slow
       path 0x82630 -> 0x82198), the `n mod 4` test at 0x821a4, strcmp (text, same) at 0x821b0 and strcmp (text, want)
       at 0x821c0 (FsRt.fr_strcmp through PC_strcmp 0x426cc), up to the A -> B boundary 0x821c4.
   In both ranges every `__asan_report_*` arm is UNTAKEN: the two stores are the only accesses, and the token engine
   (FSW_K fsw_aj_run_to_tokU over Reusable/YCbn.v) resolves each `lb` of a shadow byte to a token atom and takes the
   partial-granule slow path itself, discharging its `need` from the one shadow entry (shent) of the store's own
   address. The report sites (B; A in brackets) and the lemma whose run decides each deciding edge against the report:
     0x8262c __asan_report_store1 (0x820b0:bnez->0x82624, then 0x82628:blt) [0x824c8] - a23_seg6a (a23_st58's shent);
     0x82638 __asan_report_store1 (0x82194:bnez->0x82630, then 0x82634:blt) [0x824d4] - a23_seg89, both arms.
   The abort arms (B 0x824e4 __asan_handle_no_return; A 0x824b8) are untaken: 0x820bc `beqz a0` by text's atom fact,
   0x820c4 `bne a0, s11` by strlen (text) = En (a23_seg6b's run, a0 re-seated on s11's atom 27), 0x821b4 `bnez a0` by
   B64Canon.canonical_enc (a23_eq1). The UBSan trap 0x82180 `bltu a2, a1` -> 0x82620 (unimp) is untaken by the atom
   facts a2 = ~same in [2^64 - 1 - (2^47 - 2^23), 2^64 - 1 - 4096] and a1 = |strip| <= 3145728 (a23_tok28).

   Lane contract (crt-lane-head.md, a Theorem Labs lane): this file proves
     a23_seg6  : crt_from ss_8210c (INV_81fb8 /\ R7) -> crt_from ss_820a4 (INV_81f58 /\ R5)
     a23_seg89 : crt_from ss_821c4 INV_82068        -> crt_from ss_82180 (INV_82028 /\ R7)
   and the two frame-stability facts the loop lemmas consume, a23_stable5 = crt5_stable (crt_R5 B) and
   a23_stable7 = crt_stable7E (crt_R7 B).

   A -> B TABLE (re-measured on (internal path); "=" an equal row of crt.A2B.tsv, "~"
   mapped by meaning from both listings). The boundary names keep their A pcs (crt_INV_81f58 ...); the crt_ss_ret pcs
   are B's:
     name / fact                         A pc                              B pc
     crt_INV_81f58 / seg 6 head           0x81f58                           0x820a4 = (after B's reloads 0x82098 .. 0x820a0)
     NUL store / shadow slow path         0x81f68 / 0x824c0 .. 0x824c8      0x820b4 = / 0x82624 .. 0x8262c =
     text load                            0x81f6c `ld a0, 0x30(s1)`         0x820b8 `ld a0, 0x18(s1)` ~ (text slot 0x18)
     strlen call / return (a23_ss78)      0x81f74 / 0x81f78                 0x820c0 / 0x820c4 =
     length guard                         0x81f78 `bne a0, s6`              0x820c4 `bne a0, s11` ~ (En in s11)
     crt_INV_81fb8 / seg 7 head           0x81fb8                           0x8210c ~
     crt_INV_82028 / seg 7 exit           0x82028                           0x82180 ~
     UBSan overflow trap (B only)         -                                 0x82180 `bltu a2, a1` -> 0x82620 unimp
     NUL store / shadow slow path         0x82040 / 0x824cc .. 0x824d4      0x8219c ~ / 0x82630 .. 0x82638 =
     text into s2                         0x82044 `ld s2, 0x30(s1)`         0x821a0 `ld s2, 0x18(s1)` ~
     n mod 4 test                         0x82048 `bnez a2`                 0x821a4 `bnez a1` ~ (index in a1)
     strcmp 1 call / return (a23_ss58)    0x82054 / 0x82058                 0x821b0 / 0x821b4 =
     want into a1                         0x82060 `ld a1, 0x38(s1)`         0x821bc `ld a1, 0x30(s1)` ~ (atom 49 both)
     strcmp 2 call / crt_INV_82068        0x82064 / 0x82068                 0x821c0 / 0x821c4 =
   B DIFFERENCES FROM A (registers, slots, atoms; each changes a definition or a helper's statement, never the four
   contract lemmas' shapes):
     - frame-shadow register SF = s10 = atom 26 (A: s3 = atom 19): a23_reseat / a23_reenter / a23_strcmp_step /
       a23_cmp2 / a23_eq1 take x26 where A takes x19; crt_E's atom 26 in a23_E_agree;
     - B's atom 50 is En (crt_En, crt_nextra 19): every env agreement is below 51 (A: 50); the store-address atom of
       segs 8-9 is crt_xatom 0 = 51 (A: 50; a23_wr 51, a23_tok28, a23_SH28, a23_post28); a23_tok58 carries a fact on
       atom 50 so the token run's fresh atoms start at 51 (A's started at 50);
     - a23_INV_78 (B 0x820c4): En in s11 = x27 (A: s6 = x22), plus s6 = x22 = F and s3 = x19 = F (A read F from slot
       0x28, which B's crt_cs1e does not hold); seg 6b re-seats a0 on atom 27 and s6 on atom 47 (F) so the three slot
       stores 0x820d0 / 0x820e0 / 0x820e8 write crt_cs1's (SOff 47 _) chunks (A: two stores, 0x81f94 / 0x81f9c);
     - frame-object registers (crt_keep7 / crt_INV_82068): s11 = x27 = F + 0xe0, s7 = x23 = F + 0x80, s6 = x22 =
       F + 0x1c0, s3 = x19 = F (A: x22 F + 0xe0, x23 F + 0x80, x26 F + 0x20, x27 F + 0x1c0); a23_kept7 and the kept-
       register lists of a23_run1_post / a23_post28 gain x19;
     - loop-7 constants set by seg 6 (crt_INV_81fb8): a1 = 0, a3 = t - 1, a4 = 32, a6 = 0x100002600, a2 = ~same
       (0x820f0 `not a2, s8`, YI08.U_not), a5 = -1 (A: a0 = t, a2 = 0, a3 = 32, a4 = 0x100002600);
     - segs 8-9 index register a1 = x11 (A: a2 = x12): a23_tok28's atom 11 fact, aliases s8 + a1, the n mod 4
       condition on atom 11 (a23_mod4_bt), and the a2 = ~same atom fact for the UBSan test;
     - text slot 0x18 (A 0x30) and want slot 0x30 (A 0x38): both still atoms 48 / 49 (crt_cs1e / crt_cs1 chunks).
   The STK_RT_STR value is read through a23_STR (a computed lemma), never a numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n YN0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame FSW_rd FSW_strkit
FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site FSH_crt_cstr FSW_crt_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts B64Canon.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HState check_round_trip_loops.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YD1y YE7f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a sink instance resolved
   in this file's scope; SK is passed explicitly instead *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the runtime thunks' stack window, as a computed numeral (no STK numeral at a use site) *)
Lemma a23_STR : STK_RT_STR = ltac:(let x := eval vm_compute in STK_RT_STR in exact x).
Proof. reflexivity. Qed.

(* ================= the lane's boundary states (crt_ss_ret, agreed with a Theorem Labs lane; B pcs) ===== *)
Definition a23_ss78 : sstate := crt_ss_ret 0x820c4 crt_cs1e crt_csF.   (* the strlen thunk's return *)
Definition a23_ssb8 : sstate := crt_ss_ret 0x8210c crt_cs1 crt_csF.    (* seg 7's head, L7 takes this *)
Definition a23_ss28 : sstate := crt_ss_ret 0x82180 crt_cs1 crt_csF.    (* seg 7's exit *)
Definition a23_ss58 : sstate := crt_ss_ret 0x821b4 crt_cs1 crt_csF.    (* the first strcmp's return *)
Definition a23_ss68 : sstate := crt_ss_ret 0x821c4 crt_cs1 crt_csF.    (* the A -> B boundary, a Theorem Labs lane takes this *)

(* ---- a register is not clobbered by the seg-5 loop / is kept by the seg-7 loop ---- *)
(* raw memory equality at an address gives mbyte equality there *)
Lemma a23_mb_of_raw : forall {fx : YK11.FPState} (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros fx H m m' a E. unfold mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity | rewrite E; reflexivity].
Qed.
(* compute a register read of a closed symbolic state in the goal *)
Ltac a23_srget :=
  match goal with |- context [sr_get ?l ?r] =>
    let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e end.
Ltac a23_bvne H := apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H.
Lemma a23_nc : forall r : bv 5, In r [20; 21; 24; 25]%bv -> ~ In r crt5_clob.
Proof.
intros r Hr H. unfold crt5_clob in H. cbn [In] in Hr, H.
repeat (destruct Hr as [<-|Hr];
  [ repeat (destruct H as [H|H]; [a23_bvne H|]); exact H |]).
exact Hr.
Qed.
Lemma a23_kept7 : forall r : bv 5, In r [19; 20; 21; 22; 23; 24; 26; 27]%bv -> In r crt_kept7.
Proof.
intros r Hr. unfold crt_kept7. cbn [In] in Hr |- *.
repeat (destruct Hr as [<-|Hr]; [tauto|]). destruct Hr.
Qed.

(* ================= the two frame-stability facts the loop lemmas consume =================
   crt_keepA reads the registers 20 / 21 / 24 (and crt_R5 reads 25, crt_keep7 27 / 23 / 22 / 19), the memory of the
   text block, of the input t, of `same`'s window and of fuzz/alloc.c's statics, and nothing of md or of E. Each of
   those lies outside the loop's own write window, by crt_keepA's own separations. ---- *)
Section stab. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* a byte outside the window reads the same on both memories (crt5_stable's memory clause, as mbyte / aview) *)
Lemma a23_mem5 : forall (W3 : world tfibsegs) (m m' : word -> option byte) lo hi a,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  mbyte tfibsegs (mrestrict (w_H W3) m') a = mbyte tfibsegs (mrestrict (w_H W3) m) a /\
  aview tfibsegs (w_H W3) m' a = aview tfibsegs (w_H W3) m a.
Proof.
intros W3 m m' lo hi a H Ha Hw.
assert (E : mrestrict (w_H W3) m' (Z_to_bv 64 a) = mrestrict (w_H W3) m (Z_to_bv 64 a)).
{ unfold mrestrict. destruct (w_H W3 (Z_to_bv 64 a)); [reflexivity|]. apply H. rewrite wz by lia. exact Hw. }
assert (Em : mbyte tfibsegs (mrestrict (w_H W3) m') a = mbyte tfibsegs (mrestrict (w_H W3) m) a)
  by (unfold mbyte; rewrite E; reflexivity).
split; [exact Em|]. unfold aview. rewrite Em. reflexivity.
Qed.
Lemma a23_mem5' : forall (W3 : world tfibsegs) (m m' : word -> option byte) lo hi a,
  (forall x : word, 0 <= bv_unsigned x < 2 ^ 64 -> ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  mbyte tfibsegs (mrestrict (w_H W3) m') a = mbyte tfibsegs (mrestrict (w_H W3) m) a /\
  aview tfibsegs (w_H W3) m' a = aview tfibsegs (w_H W3) m a.
Proof.
intros W3 m m' lo hi a H Ha Hw.
apply (a23_mem5 W3 m m' lo hi a); [|exact Ha | exact Hw].
intros x Hx. apply H; [exact (u64_range x) | exact Hx].
Qed.
End stab.

(* ================= the lane's boundary-state rebuild =================
   crt_ss_ret has every register on its own atom, so a boundary is re-entered by RE-SEATING the env on the machine's
   register file (Ereg regs' (crt_extra cx)) and rebuilding the four regions on the memory there. This is the second
   half of FSH_crt_base.crt_after_call (lib/B/FSH_crt_base.v), with the callee journal dropped: it is needed at
   boundaries a RUN reaches (B 0x8210c) as well as after the runtime calls, and a run keeps no aregs_preserved; B's
   frame-shadow register is s10 = atom 26 (A: s3 = atom 19). ---- *)
Section reseat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma a23_reseat : forall cx E k ly' S' U' (W' : world tfibsegs) regs' mem' md' r cs1 csF,
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (3, c_pos cx) (frames S') ->
  YK11.getr regs' 2%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr regs' 3%bv = YK11.getr (c_regs cx) 3%bv ->
  YK11.getr regs' 4%bv = YK11.getr (c_regs cx) 4%bv ->
  YK11.getr regs' 8%bv = Z_to_bv 64 (spZ (c_regs cx)) ->
  YK11.getr regs' 9%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr regs' 26%bv = Z_to_bv 64 (crt_SF cx) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (crt_sp1 cx)) cs1 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (crt_F cx)) csF ->
  Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58) cs1 ->
  Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) csF ->
  crt_atom_chunks cs1 -> crt_atom_chunks csF ->
  YP09.region_wf (crt_slot_region cs1) = true -> YP09.region_wf (crt_frame_region csF) = true ->
  crt_E cx (Ereg regs' (crt_extra cx)) /\
  st_ok tfibsegs (Ereg regs' (crt_extra cx)) (crt_ss_ret r cs1 csF)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros cx E k ly' S' U' W' regs' mem' md' r cs1 csF HE H16 H0 Hsp0 Hsp47 HJ2 HARU' Hin3' R2 R3 R4 R8 R9 R26
  HSV HCS1 HCSF HcsF1in HcsFin HcsF1at HcsFat HWF1 HWFF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia)
  ltac:(rewrite Zminus_mod, H16; reflexivity)) as ((Flo & Fhi) & Fm32 & Fm16).
assert (Hsp1lo : spZ (c_regs cx) - 208 <= crt_sp1 cx) by (unfold crt_sp1; lia).
assert (Hsp1hi : crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
pose proof HJ2 as (HAR' & Hly' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk2 & _).
destruct Hstk2 as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Efr' : frame_addr ly' 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. destruct Hly' as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) HAR' Hin3')
  as (HF0 & HFc & HFapp).
rewrite Efr' in HF0, HFc, HFapp. rewrite crt_frame3 in HFc, HFapp.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) HAR' Hin3')
  as (Hal32' & Happ' & Hfp' & Hsp').
rewrite Efr' in Hal32', Hfp', Hsp'. rewrite crt_frame3 in Hfp', Hsp'. change (512 / 8) with 64 in Hsp'.
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
set (E' := Ereg regs' (crt_extra cx)) in *.
assert (HE' : crt_E cx E').
{ subst E'. apply crt_E_Ereg.
  - rewrite R2. apply wz. lia.
  - exact R3.
  - exact R4.
  - rewrite R8. apply wz. unfold spZ. apply u64_range.
  - rewrite R9. apply wz. lia.
  - rewrite R26. apply wz. lia. }
assert (Hag : forall n, (32 <= n < 51)%nat -> ew E' n = ew E n) by exact (crt_env_agree cx E E' HE HE').
assert (E9v : bv_unsigned (ew E' 9) = crt_sp1 cx) by (destruct HE' as (_ & _ & _ & _ & H & _); exact H).
assert (E8v : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & H & _); exact H).
assert (E26v : bv_unsigned (ew E' 26) = crt_SF cx) by (destruct HE' as (_ & _ & _ & _ & _ & H & _); exact H).
assert (E47v : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
assert (ROslot : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_slot_region cs1)).
{ unfold region_ok, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9v.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  - eapply crt_chunks_env; [exact Hag | exact HcsF1at | exact HCS1]. }
assert (ROshadow : region_ok tfibsegs E' (mrestrict (w_H W') mem') crt_shadow_region).
{ unfold region_ok, crt_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E26v.
  split; [lia|]. split; [rewrite crt_frame3; cbn [Z.div]; lia|].
  split; [|apply Forall_nil].
  intros o Ho. rewrite crt_frame3 in Ho. change (512 / 8) with 64 in Ho.
  apply (apresent_writable tfibsegs). destruct (Hsp' o ltac:(lia)) as (Hp & Hno).
  apply (fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp]. }
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_frame_region csF)).
{ unfold region_ok, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47v.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho.
    apply (apresent_writable tfibsegs). destruct (Hfp' (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp].
  - eapply crt_chunks_env; [exact Hag | exact HcsFat | exact HCSF]. }
assert (Hceil1 : alloc_ceiling <= crt_sp1 cx) by lia.
assert (Dfs : crt_F cx + 512 <= crt_SF cx \/ crt_SF cx + 64 <= crt_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [Hlow | (Hhigh & _)]).
  - left. unfold kLowShadowBeg in *. lia.
  - right. unfold crt_SF, shadow_addr, SHADOW_OFF, kHighMemBeg in *.
    Z.div_mod_to_equations. lia. }
split; [exact HE'|].
unfold crt_ss_ret.
eapply (fsw_resume_after_rtU_s0 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' U' W' mem' md' k regs' mem'
  (crt_extra cx) crt_sv_chunks (crt_ret_regions cs1 csF) crt_ret_facts r (-104) 0).
- exact HJ2.
- exact HARU'.
- exact R8.
- lia.
- lia.
- lia.
- unfold fss_ret_s0_regs, crt_ret_regions, regions_wf. cbn [forallb andb].
  rewrite HWFF, HWF1. cbn [andb]. vm_compute (YP09.region_wf crt_s0_region).
  vm_compute (YP09.region_wf crt_shadow_region). rewrite !andb_true_r. reflexivity.
- exact crt_sv_in.
- eapply crt_chunks_env; [exact Hag | exact crt_sv_atoms | exact HSV].
- intros a Ha. reflexivity.
- unfold crt_ret_regions. constructor; [exact ROslot|]. constructor; [exact ROframe|].
  constructor; [exact ROshadow | apply Forall_nil].
- apply pairwise_disjoint_of_extents.
  unfold fss_ret_s0_regs, crt_ret_regions, crt_slot_region, crt_frame_region, crt_shadow_region, crt_s0_region,
    fs_ret_s0_region.
  cbn [map]. unfold extent_of_region, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  fold E'. rewrite E8v, E9v, E47v, E26v. rewrite !crt_frame3. change (512 / 8) with 64.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try exact I;
    first [right; lia | left; lia | destruct Dfs as [Hd|Hd]; [left; lia | right; lia]].
- unfold crt_ret_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E'.
  rewrite E9v, E47v. change (2 ^ 5) with 32.
  split; [split; [lia | split; [exact Fm32 | lia]]|].
  split; [|exact I]. split; [lia | split; [exact Hal32' | lia]].
Qed.
End reseat.


(* ================= re-entering a boundary after a run =================
   The run states of this lane are crt_ss_ret without the frame's two regions (FSH_crt_site's crt_ss2 shape, with the
   slot chunks of the pc: crt_cs1e before 0x820d0, crt_cs1 after 0x820e8) plus, where the segment stores, one write region.
   At the stop pc the walk re-enters a boundary: the env moves to Ereg (ms_regs ms) (crt_extra cx) and the four regions
   are rebuilt by a23_reseat. The post-run slot region holds the boundary's chunks, possibly reordered by the stores,
   so the caller supplies the engine's list csP and `incl`. ---- *)
Section reentry. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

Definition a23_ss2 (r : Z) (cs : list YP09.chunk) : sstate :=
  mkSS r sr_atoms [crt_s0_region; crt_slot_region cs] None
    (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] []).
Lemma a23_sub2 : forall r cs csF,
  submem [crt_s0_region; crt_slot_region cs] (ss_mem (crt_ss_ret r cs csF)).
Proof.
intros r cs csF. cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions].
apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
Qed.
(* the sp facts of the walk, from crt_base alone *)
Lemma a23_spf : forall cx, crt_base B cx ->
  spZ (c_regs cx) mod 16 = 0 /\ 192 <= spZ (c_regs cx) /\
  alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47.
Proof.
intros cx HB. pose proof HB as (HPRE & _).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & _).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
split; [exact Hal16|]. split; [lia|]. split; [lia | exact H47].
Qed.
(* the write window of a run state of this lane: the s0 words and the s1 slots (crt_awr2's two arms) *)
Lemma a23_awr2 : forall cx E ly3 S3 cs, crt_base B cx -> crt_E cx E ->
  awr_ok tfibsegs B E [crt_s0_region; crt_slot_region cs] STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)).
Proof.
intros cx E ly3 S3 cs HB HE. pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
destruct (a23_spf cx HB) as (H16 & H0 & Hceil0 & H47).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
eapply awr_ok_cons_stack; [reflexivity | exact E8 | cbn; lia | cbn; lia |].
eapply awr_ok_cons_stack_off with (d := crt_sp1 cx - spZ (c_regs cx));
  [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
Qed.
(* a run from a23_ss2 r cs writes only stack bytes above alloc_ceiling *)
Lemma a23_sb : forall cx E cs (m m' : word -> option byte),
  crt_base B cx -> crt_E cx E -> frame_of E [crt_s0_region; crt_slot_region cs] m m' ->
  same_below m m' alloc_ceiling.
Proof.
intros cx E cs m m' HB HE HF x Hx. pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
destruct (a23_spf cx HB) as (H16 & H0 & Hceil0 & H47).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
apply HF. rewrite (wz x) by lia. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<-|[<-|[]]]; cbn [crt_s0_region fs_ret_s0_region crt_slot_region YP09.r_base YP09.r_wlo YP09.r_whi
  base_val] in Hr; [rewrite E8 in Hr | rewrite E9 in Hr]; lia.
Qed.

(* the boundary at the stop pc, rebuilt from the engine's state *)
Lemma a23_reenter : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms mdC ssC r1 cs1' csP,
  crt_base B cx -> crt_E cx E ->
  st_ok tfibsegs E ssC (restrict (w_H W3) ms) -> ss_pc ssC = r1 -> ss_resv ssC = None ->
  nth_error (ss_mem ssC) 0 = Some crt_s0_region ->
  nth_error (ss_mem ssC) 1 = Some (crt_slot_region csP) ->
  incl cs1' csP ->
  Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58) cs1' ->
  crt_atom_chunks cs1' -> YP09.region_wf (crt_slot_region cs1') = true ->
  sr_get (ss_regs ssC) 2%bv = SOff 2 0 -> sr_get (ss_regs ssC) 3%bv = SOff 3 0 ->
  sr_get (ss_regs ssC) 4%bv = SOff 4 0 -> sr_get (ss_regs ssC) 8%bv = SOff 8 0 ->
  sr_get (ss_regs ssC) 9%bv = SOff 9 0 -> sr_get (ss_regs ssC) 26%bv = SOff 26 0 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crt_csF ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) mdC k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) mdC ->
  In (3, c_pos cx) (frames S3) ->
  crt_E cx (Ereg (ms_regs ms) (crt_extra cx)) /\
  st_ok tfibsegs (Ereg (ms_regs ms) (crt_extra cx)) (crt_ss_ret r1 cs1' crt_csF) (restrict (w_H W3) ms).
Proof.
intros cx E k ly3 S3 U3 W3 ms mdC ssC r1 cs1' csP HB HE HS Hpc Hres H0r H1r Hincl Hin1 Hat1 Hwf1
  G2 G3 G4 G8 G9 G26 HCSF HJ HARU Hin3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (a23_spf cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
assert (RG : forall q : bv 5, YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs ssC) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W3) E ssC ms q HS)).
assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
  by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite RG, G2, fsw_SOff0; apply V; [exact E2 | lia]).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = YK11.getr (c_regs cx) 3%bv)
  by (rewrite RG, G3, fsw_SOff0; exact E3).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = YK11.getr (c_regs cx) 4%bv)
  by (rewrite RG, G4, fsw_SOff0; exact E4).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
  by (rewrite RG, G8, fsw_SOff0; apply V; [exact E8 | unfold spZ; apply u64_range]).
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite RG, G9, fsw_SOff0; apply V; [exact E9 | lia]).
assert (R26 : YK11.getr (ms_regs ms) 26%bv = Z_to_bv 64 (crt_SF cx))
  by (rewrite RG, G26, fsw_SOff0; apply V; [exact E26 | pose proof (u64_range (ew E 26)); lia]).
assert (HR0 : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) crt_s0_region)
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 0 crt_s0_region HS H0r).
assert (HRs : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_slot_region csP))
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 1 (crt_slot_region csP) HS H1r).
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (spZ (c_regs cx))) crt_sv_chunks).
{ destruct HR0 as (_ & _ & _ & Hc). cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E8 in Hc. exact Hc. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) cs1').
{ destruct HRs as (_ & _ & _ & Hc). cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E9 in Hc. rewrite Forall_forall in Hc |- *. intros c Hc'. exact (Hc c (Hincl c Hc')). }
assert (HcsFin : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\
    YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) crt_csF)
  by (unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil]).
assert (HcsFat : crt_atom_chunks crt_csF)
  by (unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]).
assert (HwfF : YP09.region_wf (crt_frame_region crt_csF) = true) by (vm_compute; reflexivity).
pose proof (crt_mkst (w_H W3) E ssC ms HS Hres) as Ems. rewrite Hpc in Ems.
destruct (a23_reseat SK B cx E k ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdC r1 cs1' crt_csF
  HE H16 H0 Hceil0 H47 HJ HARU Hin3 R2 R3 R4 R8 R9 R26 HSV HCS1 HCSF Hin1 HcsFin Hat1 HcsFat Hwf1 HwfF)
  as (HE' & HS').
split; [exact HE'|]. rewrite Ems at 2. exact HS'.
Qed.
End reentry.

(* ================= crt_keepA under a memory frame =================
   crt_keepA reads memory only in four places: text's block [text - HEAD, text + enc_size len), the input
   [t, t + |tb| + 1), `same`'s window [same, same + |tb| + 1) and fuzz/alloc.c's four statics, which lie in the image
   below 0x5fd000. A step that keeps those bytes (and the registers 20 / 21 / 24) keeps crt_keepA. Both loop windows
   miss all four, by crt_keepA's own separations; so does every run and runtime call of this lane, whose writes are
   stack bytes at or above alloc_ceiling. ---- *)
Section keepfr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Definition a23_rd (cx : crt_cx) (a : Z) : Prop :=
  c_text cx - HEAD <= a < c_text cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) \/
  c_t cx <= a < c_t cx + Z.of_nat (length (c_tb cx)) + 1 \/
  0x10000 <= a < 0x5fd000 \/
  SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44.

Lemma a23_strip_len0 : forall l, (length (B64Canon.b64_strip l) <= length l)%nat.
Proof.
intros l. unfold B64Canon.b64_strip. induction l as [|c l IH].
- simpl. lia.
- simpl. destruct (negb (b64_ws c)); simpl; lia.
Qed.
Lemma a23_zs_len0 : forall tb, length (HState.zs tb) = length tb.
Proof. intros tb. unfold HState.zs. apply length_map. Qed.
(* the image's hull is [0x10000, FS_IMG_END), so a byte below it or at/after it is not an image byte; base v30's
   image disjunction places `same` and `want` in one of those two zones *)
Lemma a23_img_lo : forall a, in_img tfibsegs a -> 0x10000 <= a.
Proof.
intros a (sg & Hin & Hr).
assert (Hx : forallb (fun sg0 => 0x10000 <=? Z.of_N (seg_base sg0)) tfibsegs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hx. pose proof (Hx sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
Lemma a23_not_img : forall a, (a < 0x10000 \/ 0x5fd000 <= a) -> ~ in_img tfibsegs a.
Proof.
intros a Ha Hin. pose proof (a23_img_lo a Hin). pose proof (fs_segs_img a Hin). unfold FS_IMG_END in *. lia.
Qed.
(* the whole shadow band lies below alloc_ceiling *)
Lemma a23_band_lt_ceil : SHADOW_OFF + 2 ^ 44 <= alloc_ceiling.
Proof.
pose proof (proj1 (@alloc_ceiling_val rc)) as HA. vm_compute YM05.CEIL_MIN in HA. unfold SHADOW_OFF. lia.
Qed.
(* the shadow of the n cell's granule is a shadow-band address (crt_keepA's new conjunct, base v28) *)
Lemma a23_shadow_band : forall (F x : Z), 4096 <= F -> F + 512 <= alloc_ceiling -> F + 0x1c0 <= x < F + 0x1c0 + 8 ->
  0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44.
Proof.
intros F x H1 H2 H3. pose proof (proj1 (@alloc_ceiling_val rc)) as HA. vm_compute YM05.CEIL_MAX in HA.
unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.
(* the arithmetic of a23_rd_facts, in a small context *)
Lemma a23_rd_num : forall (text enc t n want En same strip ac a : Z),
  4096 <= text - 16 -> text + enc <= ac -> 4096 <= t -> t + n + 1 <= ac ->
  0 <= enc -> 0 <= n -> 0 <= En -> 0 <= strip <= n ->
  (want + En + 1 <= text - 16 \/ text + enc <= want) ->
  (same + n + 1 <= text - 16 \/ text + enc <= same) ->
  (want + En + 1 <= t \/ t + n + 1 <= want) -> (same + n + 1 <= t \/ t + n + 1 <= same) ->
  (want + En + 1 <= 0x10000 \/ 0x5fd000 <= want) -> (same + n + 1 <= 0x10000 \/ 0x5fd000 <= same) ->
  0x5fd000 <= ac ->
  (text - 16 <= a < text + enc \/ t <= a < t + n + 1 \/ 0x10000 <= a < 0x5fd000) ->
  0 <= a < ac /\ a <> want + En /\ a <> same + strip.
Proof. intros. lia. Qed.
(* what crt_keepA says about the addresses a23_rd names: they are machine addresses below alloc_ceiling, and neither
   of the lane's two store addresses (want + En, same + |strip|) is one of them *)
Lemma a23_rd_facts : forall cx same k ly3 S3 U3 (W3 : world tfibsegs) ms3,
  crt_keepA B cx same k ly3 S3 U3 W3 ms3 ->
  forall a, a23_rd cx a -> 0 <= a < alloc_ceiling /\
    a <> c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 /\
    a <> same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))).
Proof.
intros cx same k ly3 S3 U3 W3 ms3 HK a Hr.
pose proof a23_band_lt_ceil as HBC.
pose proof (proj1 (@alloc_ceiling_val rc)) as HA. vm_compute YM05.CEIL_MIN in HA.
destruct HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & _ & _ & _ & _ & _ & _
  & _ & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & _).
cbn zeta in Ks1, Ks2, HX1, HX2, HI1, HI2, Kd2, Kd3, Kd4, Kd5, Kp1, Kp2, Kwu, Ksh1, Ksh2.
pose proof (a23_strip_len0 (HState.zs (c_tb cx))) as SL. rewrite a23_zs_len0 in SL.
pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)) as HDP.
pose proof (Nat2Z.is_nonneg (length (c_bs cx))) as HL0.
pose proof (Nat2Z.is_nonneg (length (c_tb cx))) as HL1.
pose proof (Nat2Z.is_nonneg (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) as HL2.
unfold a23_rd in Hr.
unfold HEAD, FSH_Fn_writer.enc_size, FS_IMG_END in HX1, HX2, Kd2, Kd3, Kd4, Kd5, Kp1, Kp2, Hr.
destruct Hr as [Hrr|[Hrr|[Hrr|Hsh]]];
  [ exact (a23_rd_num (c_text cx) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) (c_t cx)
      (Z.of_nat (length (c_tb cx))) (c_want cx) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) same
      (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) alloc_ceiling a
      HX1 HX2 HI1 HI2 ltac:(lia) HL1 ltac:(lia) ltac:(lia) Kd2 Kd3 Kd4 Kd5 Kp1 Kp2 ltac:(lia) ltac:(tauto))
  | exact (a23_rd_num (c_text cx) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) (c_t cx)
      (Z.of_nat (length (c_tb cx))) (c_want cx) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) same
      (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) alloc_ceiling a
      HX1 HX2 HI1 HI2 ltac:(lia) HL1 ltac:(lia) ltac:(lia) Kd2 Kd3 Kd4 Kd5 Kp1 Kp2 ltac:(lia) ltac:(tauto))
  | exact (a23_rd_num (c_text cx) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) (c_t cx)
      (Z.of_nat (length (c_tb cx))) (c_want cx) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) same
      (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) alloc_ceiling a
      HX1 HX2 HI1 HI2 ltac:(lia) HL1 ltac:(lia) ltac:(lia) Kd2 Kd3 Kd4 Kd5 Kp1 Kp2 ltac:(lia) ltac:(tauto))
  | refine (conj _ (conj _ _));
    [ assert (HS0 : 0 <= SHADOW_OFF) by (unfold SHADOW_OFF; lia); lia
    | intros Heq; rewrite Heq in Hsh;
      exact (Ksh1 (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) ltac:(lia) Hsh)
    | intros Heq; rewrite Heq in Hsh;
      exact (Ksh2 (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) ltac:(lia) Hsh) ] ].
Qed.
(* want's lower bound, from its block (the segments have ARU; base v30 dropped keepA's own `0x5fd000 <= want`) *)
Lemma a23_want_lo : forall cx same k ly3 S3 U3 (W3 : world tfibsegs) ms3 mem md,
  ARU tfibsegs B ly3 S3 U3 W3 mem md -> crt_keepA B cx same k ly3 S3 U3 W3 ms3 -> 4096 <= c_want cx.
Proof.
intros cx same k ly3 S3 U3 W3 ms3 mem md HARU HK.
destruct HK as (_ & _ & _ & KP & _). cbn zeta in KP.
assert (HinW : In (c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; right; cbn [In]; tauto).
destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) ly3 S3 W3 (unpoison U3 mem) md _ _
  (ARU_AR tfibsegs B ly3 S3 U3 W3 mem md HARU) HinW) as (_ & H4 & _).
exact H4.
Qed.
Lemma a23_keepA_keep : forall cx same k ly3 S3 U3 (W3 : world tfibsegs) (ms ms' : machine_state),
  4096 <= crt_F cx -> crt_F cx + 512 <= alloc_ceiling ->
  (forall a, 0 <= a < 2 ^ 64 -> a23_rd cx a ->
     mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms')) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a) ->
  (forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
     writable_at tfibsegs (mrestrict (w_H W3) (ms_mem ms')) a) ->
  (forall r : bv 5, In r [20; 21; 24]%bv -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r) ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms -> crt_keepA B cx same k ly3 S3 U3 W3 ms'.
Proof.
intros cx same k ly3 S3 U3 W3 ms ms' HFB1 HFB2 HM HW HR HK.
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV0.
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
assert (MB : forall a, 0 <= a < 2 ^ 64 -> a23_rd cx a ->
  mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms')) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a)
  by exact HM.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> a23_rd cx a ->
  aview tfibsegs (w_H W3) (ms_mem ms') a = aview tfibsegs (w_H W3) (ms_mem ms) a)
  by (intros a Ha Hr; unfold aview; rewrite (MB a Ha Hr); reflexivity).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2 & K12
  & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & KWLO & KWU & K23 & K24 & KRA).
cbn zeta in *.
(* the lengths of the two byte lists crt_keepA holds *)
assert (LT : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx) ++ [0])) =
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, (check_round_trip_loops.enc_len_Z (c_bs cx)).
  unfold FSH_Fn_writer.enc_size. cbn [Z.of_nat]. lia. }
assert (LI : Z.of_nat (length (HState.zs (c_tb cx ++ [Z_to_bv 8 0]))) = Z.of_nat (length (c_tb cx)) + 1).
{ unfold HState.zs. rewrite length_map, length_app. cbn [length]. lia. }
(* text's block and the input lie in memory: four numeric bounds the caller supplies (from ARU in a segment, from
   crt_keepA's own text / t bounds in the stability facts) *)
assert (HTX : forall a, c_text cx - HEAD <= a < c_text cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) ->
  0 <= a < 2 ^ 64) by (intros a Ha; unfold HEAD in *; lia).
assert (HTI : forall a, c_t cx <= a < c_t cx + Z.of_nat (length (c_tb cx)) + 1 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; lia).
split; [rewrite (HR 20%bv ltac:(cbn; tauto)); exact K1|].
split; [rewrite (HR 21%bv ltac:(cbn; tauto)); exact K2|].
split; [rewrite (HR 24%bv ltac:(cbn; tauto)); exact K3|].
split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
split.
{ destruct K7 as (H7a & H7b & H7c & H7d). split; [exact H7a|]. split; [exact H7b|]. split; [exact H7c|].
  apply (val_mem_kept tfibsegs (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') (c_text cx - HEAD) 8
    (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))); [|exact H7d].
  intros j Hj. apply AV; [apply HTX; unfold HEAD, FSH_Fn_writer.enc_size in *; lia
                         | left; unfold HEAD, FSH_Fn_writer.enc_size in *; lia]. }
split.
{ apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) (ms_mem ms'))); [exact K8|].
  intros a Ha. rewrite LT in Ha. apply MB; [apply HTX; unfold HEAD in *; lia | left; unfold HEAD in *; lia]. }
split.
{ apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) (ms_mem ms'))); [exact K9|].
  intros a Ha. rewrite LI in Ha.
  assert (H64 : 0 <= a < 2 ^ 64) by (apply HTI; lia).
  apply MB; [exact H64 | right; left; lia]. }
split; [exact K10|]. split; [exact K11|].
split; [exact HX1|]. split; [exact HX2|]. split; [exact HI1|]. split; [exact HI2|].
split; [exact KF1|]. split; [exact KF2|].
split.
{ intros a Ha. destruct (K12 a Ha) as (Hw & Haw). split; [exact (HW a Ha) | exact Haw]. }

split.
{ destruct K13 as (live & peak & cnt & Hg & Hlv & Hcn). exists live, peak, cnt.
  split; [|split; [exact Hlv | exact Hcn]].
  destruct Hg as (G1 & G2 & G3 & G4 & Gb).
  assert (GV : forall g, g = G_LIVE \/ g = G_PEAK \/ g = G_COUNT \/ g = G_FAIL ->
    forall v, val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) g 8 v ->
              val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms')) g 8 v).
  { intros g Hg' v Hv.
    apply (val_mem_kept tfibsegs (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') g 8 v); [|exact Hv].
    intros j Hj. apply AV; unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *;
      [destruct Hg' as [->|[->|[->| ->]]]; lia
      | right; right; left; destruct Hg' as [->|[->|[->| ->]]]; lia]. }
  split; [exact (GV G_LIVE ltac:(tauto) live G1)|].
  split; [exact (GV G_PEAK ltac:(tauto) peak G2)|].
  split; [exact (GV G_COUNT ltac:(tauto) cnt G3)|].
  split; [exact (GV G_FAIL ltac:(tauto) SIZE_MAXZ G4) | exact Gb]. }
split; [exact K14|]. split; [exact K15|]. split; [exact K16|]. split; [exact K17|]. split; [exact K18|].
split; [exact K19|]. split; [exact K20|]. split; [exact K21|]. split; [exact K22|].
split; [exact KWLO|]. split; [exact KWU|].
split; [exact K23|]. split; [exact K24|].
intros x Hx. destruct (KRA x Hx) as (sb & Hsb & Hok). exists sb. split; [|exact Hok].
rewrite <- Hsb. destruct (a23_shadow_band (crt_F cx) x HFB1 HFB2 Hx) as (HB1 & HB2).
apply AV; [exact HB1 | right; right; right; exact HB2].
Qed.
End keepfr.

(* ================= the two frame-stability facts the loop lemmas consume =================
   crt5_stable (crt_R5 B) for the encode loop (window [want, want + En), registers crt5_clob, env atoms from 50 on,
   md unrelated) and crt_stable7 (crt_R7 B) for the canonical loop (window [same, same + |tb| + 1), registers off
   crt_kept7). Neither crt_R5 nor crt_R7 reads E or md, so only the registers and the memory matter, and crt_keepA's
   own separations put every byte it reads outside both windows. ---- *)
Section stab2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* a window named by a register value is the SAME window as the one crt_keepA names, or it misses the machine's
   address space entirely: w64 is injective only modulo 2 ^ 64 *)
Lemma a23_w64_mod : forall x y : Z, w64 x = w64 y -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
intros x y H. apply (f_equal (@bv_unsigned 64)) in H. unfold w64 in H.
rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Lemma a23_same_cases : forall same same0 n,
  w64 same = w64 same0 -> 4096 <= same -> same + n + 1 <= alloc_ceiling -> 0 <= n ->
  same = same0 \/ (forall a, 0 <= a < 2 ^ 64 -> ~ (same0 <= a < same0 + n + 1)).
Proof.
intros same same0 n H H1 H2 Hn. pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
destruct (Z.eq_dec same same0) as [->|Hne]; [left; reflexivity|]. right.
assert (Hd : (2 ^ 64 | same0 - same)).
{ apply Z.mod_divide; [lia|]. rewrite Zminus_mod, <- (a23_w64_mod same same0 H), Z.sub_diag. reflexivity. }
destruct Hd as (q & Hq).
assert (Hq0 : q <> 0) by (intros ->; apply Hne; lia).
intros a Ha Hin.
destruct (Z.le_gt_cases 1 q) as [Hpos|Hneg].
- assert (2 ^ 64 <= q * 2 ^ 64) by nia. lia.
- assert (q <= -1) by lia. assert (q * 2 ^ 64 <= - (2 ^ 64)) by nia. lia.
Qed.

Lemma a23_stable5 : crt5_stable (crt_R5 B).
Proof.
intros cx E E' k ly3 S3 U3 W3 ms ms' md md' Hag Hreg Hmem Hgr HR5.
destruct HR5 as (same & H25 & HK).
pose proof HK as HK'.
destruct HK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & K11 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2 & K12 & _ & _ & _
  & _ & K17 & _ & K19 & _ & K21 & _ & _ & _ & Ksh1 & _ & _).
cbn zeta in *.
exists same. split.
- rewrite (Hreg 25%bv (a23_nc 25%bv ltac:(cbn [In]; tauto))). exact H25.
- apply (a23_keepA_keep B cx same k ly3 S3 U3 W3 ms ms' KF1 KF2).
  + intros a Ha Hr. apply a23_mb_of_raw. apply Hmem. rewrite (wz a ltac:(lia)).
    destruct Hr as [Ht | [Hi | [Hs | Hsh]]]; unfold HEAD, FSH_Fn_writer.enc_size in *;
      [lia | lia | unfold FS_IMG_END in *; lia | intros Hin; exact (Ksh1 a ltac:(lia) Hsh)].
  + intros a Ha. eapply writable_at_grows; [exact Hgr | exact (proj1 (K12 a Ha))].
  + intros r Hr. apply Hreg. apply a23_nc. cbn [In] in Hr |- *. tauto.
  + exact HK.
Qed.

Lemma a23_stable7 : crt_stable7E (crt_R7 B).
Proof.
intros cx E E' k ly3 S3 U3 W3 ms3 md3 ms3' md3' same0 HEa HEb H24 HR7 HW7.
destruct HR7 as (same & HK & HK7).
destruct HW7 as (Hkept & Hmem & Hwr).
pose proof HK as HK'.
destruct HK' as (_ & _ & K3 & _ & _ & _ & _ & _ & _ & K10 & K11 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2 & K12 & _ & _ & _
  & K16 & _ & K18 & _ & K20 & K21 & K22 & KWLO & KWU & _ & Ksh2 & _).
cbn zeta in *.
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
assert (HEQ : w64 same = w64 same0) by (rewrite <- K3; exact H24).
destruct (a23_same_cases same same0 (Z.of_nat (length (c_tb cx))) HEQ K10 K11 ltac:(lia)) as [Esame | Hout].
- (* the loop's window is crt_keepA's own `same` window *)
  exists same. split.
  + apply (a23_keepA_keep B cx same k ly3 S3 U3 W3 ms3 ms3' KF1 KF2).
    * intros a Ha Hr. apply a23_mb_of_raw. apply Hmem; [lia|]. rewrite <- Esame.
      destruct Hr as [Ht | [Hi | [Hs | Hsh]]]; unfold HEAD, FSH_Fn_writer.enc_size in *;
        [lia | lia | unfold FS_IMG_END in *; lia | intros Hin; exact (Ksh2 a ltac:(lia) Hsh)].
    * intros a Ha. rewrite <- Esame in Hwr. exact (Hwr a Ha).
    * intros r Hr. apply Hkept. apply a23_kept7. cbn [In] in Hr |- *. tauto.
    * exact HK.
  + destruct HK7 as (P27 & P23 & P22 & P19 & Pw). cbn zeta in *.
    split; [rewrite (Hkept 27%bv (a23_kept7 27%bv ltac:(cbn [In]; tauto))); exact P27|].
    split; [rewrite (Hkept 23%bv (a23_kept7 23%bv ltac:(cbn [In]; tauto))); exact P23|].
    split; [rewrite (Hkept 22%bv (a23_kept7 22%bv ltac:(cbn [In]; tauto))); exact P22|].
    split; [rewrite (Hkept 19%bv (a23_kept7 19%bv ltac:(cbn [In]; tauto))); exact P19|].
    apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms3'))); [exact Pw|].
    intros a Ha.
    assert (LW : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx) ++ [0]))
                 = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1).
    { rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, (check_round_trip_loops.enc_len_Z (c_bs cx)).
      cbn [Z.of_nat]. lia. }
    rewrite LW in Ha.
    assert (ME : ms_mem ms3' (Z_to_bv 64 a) = ms_mem ms3 (Z_to_bv 64 a)).
    { apply Hmem; [lia|]. rewrite <- Esame. destruct K16 as [Hd|Hd]; lia. }
    unfold mbyte, mrestrict. destruct (w_H W3 (Z_to_bv 64 a)); [reflexivity | rewrite ME; reflexivity].
- (* the loop's window misses the machine's addresses, so the whole memory is kept *)
  assert (MEall : forall a, 0 <= a < 2 ^ 64 -> ms_mem ms3' (Z_to_bv 64 a) = ms_mem ms3 (Z_to_bv 64 a))
    by (intros a Ha; apply Hmem; [lia | exact (Hout a Ha)]).
  assert (MEw : forall x : word, ms_mem ms3' x = ms_mem ms3 x).
  { intros x. pose proof (u64_range x) as Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1 2.
    apply MEall. exact Hx. }
  assert (MG : mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms3'))).
  { intros x Hnn. unfold mrestrict in *. destruct (w_H W3 x); [exact Hnn|]. rewrite MEw. exact Hnn. }
  exists same. split.
  + apply (a23_keepA_keep B cx same k ly3 S3 U3 W3 ms3 ms3' KF1 KF2).
    * intros a Ha Hr. apply a23_mb_of_raw. apply MEall. exact Ha.
    * intros a Ha. eapply writable_at_grows; [exact MG | exact (proj1 (K12 a Ha))].
    * intros r Hr. apply Hkept. apply a23_kept7. cbn [In] in Hr |- *. tauto.
    * exact HK.
  + destruct HK7 as (P27 & P23 & P22 & P19 & Pw). cbn zeta in *.
    split; [rewrite (Hkept 27%bv (a23_kept7 27%bv ltac:(cbn [In]; tauto))); exact P27|].
    split; [rewrite (Hkept 23%bv (a23_kept7 23%bv ltac:(cbn [In]; tauto))); exact P23|].
    split; [rewrite (Hkept 22%bv (a23_kept7 22%bv ltac:(cbn [In]; tauto))); exact P22|].
    split; [rewrite (Hkept 19%bv (a23_kept7 19%bv ltac:(cbn [In]; tauto))); exact P19|].
    apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms3'))); [exact Pw|].
    intros a Ha. unfold mbyte, mrestrict.
    destruct (w_H W3 (Z_to_bv 64 a)); [reflexivity | rewrite MEw; reflexivity].
Qed.

End stab2.

(* the conjunction of two boundary invariants, as the walk's lanes pass them (INV /\ R) *)
Definition a23_and (P Q : crt_inv) : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => P cx E k ly3 S3 U3 W3 ms3 md3 /\ Q cx E k ly3 S3 U3 W3 ms3 md3.

(* ================= segment 6's run state: the boundary at B 0x820a4 plus the store's own byte =================
   The `sb zero, 0(a0)` at 0x820b4 writes ONE byte, at a0 = want + En, and its ASan check reads that byte's shadow.
   The run state is therefore the boundary without the frame's two regions (their bytes are not touched and their
   windows would break the token engine's cells_safe_b, since the frame's shadow lies in the shadow band) plus a
   one-byte write region at the a0 atom, and one shadow entry for it. The engine then takes the partial-granule slow
   path 0x82628 -> 0x820b4 itself and never reaches __asan_report_store1 at 0x8262c. B only: the fact on atom 50
   (En, crt_E's last extra atom) puts the token run's fresh atoms at 51 and up, so the run keeps crt_E. ---- *)
Definition a23_wr (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 1 [].
Definition a23_af : afact := mkAF 4096 140737479966720 0.
Definition a23_shb : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
Definition a23_en : afact := mkAF 0 140737479966720 0.
Definition a23_base58 : sstate :=
  mkSS 0x820a4 (sr_set sr_atoms 18%bv (SOff 32 0))
    (a23_wr 10 :: [crt_s0_region; crt_slot_region crt_cs1e]) None
    (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] []).
Definition a23_tok58 : sstate :=
  add_atom (add_atom (add_atom (add_atom a23_base58 48%nat a23_af) 10%nat a23_af) 32%nat a23_shb) 50%nat a23_en.
Definition a23_SH58 : list shent := [mkSHE 10 0 1].

Section seg6. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* the walk's env facts survive the token run's fresh atoms (they live below 51; B's atom 50 is En) *)
Lemma a23_E_agree : forall cx E E', env_agree 51 E E' -> crt_E cx E -> crt_E cx E'.
Proof.
intros cx E E' Hag HE.
assert (A : forall n, (n < 51)%nat -> ew E' n = ew E n) by (intros n Hn; apply (proj1 Hag); lia).
destruct HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
split; [rewrite (A 2%nat ltac:(lia)); exact E2|].
split; [rewrite (A 3%nat ltac:(lia)); exact E3|].
split; [rewrite (A 4%nat ltac:(lia)); exact E4|].
split; [rewrite (A 8%nat ltac:(lia)); exact E8|].
split; [rewrite (A 9%nat ltac:(lia)); exact E9|].
split; [rewrite (A 26%nat ltac:(lia)); exact E26|].
intros j Hj. rewrite (A (32 + j)%nat ltac:(unfold crt_nextra in Hj; lia)). exact (EX j Hj).
Qed.

(* the run state and its shadow entry, from the boundary at B 0x820a4 *)
Lemma a23_st58 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E ->
  crt_INV_81f58 B cx E k ly3 S3 U3 W3 ms3 md3 ->
  4096 <= c_text cx -> c_text cx <= alloc_ceiling ->
  st_ok tfibsegs E (crt_ss_ret 0x820a4 crt_cs1e crt_csF) (restrict (w_H W3) ms3) ->
  st_ok tfibsegs E a23_tok58 (restrict (w_H W3) ms3) /\
  sh_ok tfibsegs fs_Bx a23_SH58 E (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HI HT1 HT2 HS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
destruct HI as (I10 & I18 & I27 & I22 & I19 & IZ & Iw1 & Iw2 & Ish & Iwin & IFd & IRA & IWR & IAW).
cbn zeta in I10, I18, I27, I22, I19, IZ, Iw1, Iw2, Ish, Iwin, IFd, IRA, IWR, IAW.
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
(* the env's atoms 10, 32 and 48 *)
assert (A10 : YK11.getr (ms_regs ms3) 10%bv = ew E 10)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (EA10 : ew E 10 = w64 (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)) by (rewrite <- A10; exact I10).
assert (EV10 : bv_unsigned (ew E 10) = c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
  by (rewrite EA10; unfold w64; apply wz; lia).
assert (A18 : YK11.getr (ms_regs ms3) 18%bv = ew E 18)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (crt_E_shadow cx E HE).
assert (EV32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
assert (E48 : ew E 48 = Z_to_bv 64 (c_text cx)) by exact (crt_E_text cx E HE).
assert (EV48 : bv_unsigned (ew E 48) = c_text cx) by (rewrite E48; apply wz; lia).
assert (EV50 : bv_unsigned (ew E 50) = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4).
{ rewrite (crt_E_En cx E HE). unfold crt_En. apply wz.
  pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)). lia. }
(* the state: drop the frame's regions, re-seat s2 on the shadow atom, add the store's region and four facts *)
pose proof (st_ok_submem tfibsegs E _ _ _ HS (a23_sub2 0x820a4 crt_cs1e crt_csF)
  ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (a23_ss2 0x820a4 crt_cs1e) (restrict (w_H W3) ms3)) in HS2.
assert (HS3 : st_ok tfibsegs E
  (mkSS (ss_pc (a23_ss2 0x820a4 crt_cs1e)) (sr_set (ss_regs (a23_ss2 0x820a4 crt_cs1e)) 18%bv (SOff 32 0))
     (ss_mem (a23_ss2 0x820a4 crt_cs1e)) (ss_resv (a23_ss2 0x820a4 crt_cs1e))
     (ss_facts (a23_ss2 0x820a4 crt_cs1e))) (restrict (w_H W3) ms3)).
{ apply (st_ok_set_reg tfibsegs E _ _ 18%bv (SOff 32 0) HS2).
  - intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
  - cbn [ms_regs restrict]. rewrite fsw_SOff0, E32, I18. reflexivity. }
assert (HRW : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (a23_wr 10)).
{ unfold region_ok, a23_wr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EV10.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + o)
    with (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) by lia. exact IWR. }
assert (HS4 : st_ok tfibsegs E a23_base58 (restrict (w_H W3) ms3)).
{ apply (st_ok_add_region' tfibsegs E _ _ (a23_wr 10) HS3 ltac:(vm_compute; reflexivity)).
  - cbn [ms_mem restrict]. exact HRW.
  - apply all_disjoint_of_extents.
    unfold a23_ss2. cbn [ss_mem map].
    unfold extent_of_region, base_val, a23_wr, crt_s0_region, fs_ret_s0_region, crt_slot_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite EV10, E8, E9.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I; first [left; lia | right; lia]. }
split.
- unfold a23_tok58.
  apply (st_ok_add_fact tfibsegs E _ _ 50%nat a23_en);
    [apply (st_ok_add_fact tfibsegs E _ _ 32%nat a23_shb);
       [apply (st_ok_add_fact tfibsegs E _ _ 10%nat a23_af);
          [apply (st_ok_add_fact tfibsegs E _ _ 48%nat a23_af); [exact HS4|] | ] | ] | ];
    unfold afact_ok, a23_af, a23_shb, a23_en; cbn [af_lo af_hi af_al2].
  + rewrite EV48. split; [lia | split; [apply Z.mod_1_r | lia]].
  + rewrite EV10. split; [lia | split; [apply Z.mod_1_r | lia]].
  + rewrite EV32. split; [lia | split; [apply Z.mod_1_r | lia]].
  + rewrite EV50. pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)).
    split; [lia | split; [apply Z.mod_1_r | lia]].
- unfold sh_ok, a23_SH58. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range tfibsegs (w_H W3) (ms_mem ms3) E fs_Bx 10
    (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) 1
    (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) 0 1).
  + exact IRA.
  + unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
  + apply (U_atom E 10 _ EA10). lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. apply Ish. lia.
Qed.


End seg6.

(* ================= the lane's inner boundary B 0x820c4 (A 0x81f78) =================
   The strlen thunk returns at 0x820c4 with a0 = |text| = En. What the stretch 0x820c4 .. 0x8210c then reads is this,
   and nothing else: a0 = s11 = En (the guard `bne a0, s11` at 0x820c4, whose taken arm is the abort 0x824e4; A: s6),
   s2 the shadow base, s9 = t (0x820f4 `addi a3, s9, -1`, and s9 is loop 7's cursor), s6 = F (the frame-object addresses
   0x820cc .. 0x820ec; A loaded F from slot 0x28), s3 = F (crt_keep7's, the epilogue's), s8 = same (0x820f0 `not a2,
   s8`; crt_keepA's x24), want's bytes with the NUL this lane's first store wrote, and crt_keepA. ---- *)
Section seg6b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Definition a23_INV_78 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let r := ms_regs ms3 in let len := Z.of_nat (length (c_bs cx)) in
  YK11.getr r 10%bv = w64 ((len + 2) / 3 * 4) /\ YK11.getr r 18%bv = w64 SHADOW_OFF /\
  YK11.getr r 27%bv = w64 ((len + 2) / 3 * 4) /\ YK11.getr r 25%bv = w64 (c_t cx) /\
  YK11.getr r 22%bv = w64 (crt_F cx) /\ YK11.getr r 19%bv = w64 (crt_F cx) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) (c_want cx) (WriterSpec.b64_enc (c_bs cx) ++ [0]) /\
  (exists same, crt_keepA B cx same k ly3 S3 U3 W3 ms3).

(* two conjuncts of crt_base the poison clauses read: the input's live block, and that the input overlaps no
   user-poisoned head of the entry (crt_base's LAST conjunct, check_round_trip_spec's premise since base v26) *)
Lemma a23_base_inblk : forall cx, crt_base B cx ->
  exists pt kt, In (pt, kt) (ablocks B (c_ly cx) (c_S cx)) /\ pt <= c_t cx /\
    c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= pt + kt.
Proof.
intros cx HB. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIB & _). exact HIB.
Qed.
Lemma a23_base_ut : forall cx, crt_base B cx ->
  Forall (fun q => c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= fst q \/ fst q + snd q <= c_t cx) (c_U cx).
Proof.
intros cx HB. unfold crt_base in HB.
repeat match type of HB with _ /\ _ => destruct HB as [_ HB] end. exact HB.
Qed.

(* a block of the entry and one of the walk's three fresh blocks, at the head of a permutation of the live blocks *)
Lemma a23_perm2 : forall (L' L extra : list (Z * Z)) x y,
  Permutation L' (L ++ extra) -> In x L -> In y extra -> exists rest, Permutation L' (x :: y :: rest).
Proof.
intros L' L extra x y HP Hx Hy.
destruct (in_split x L Hx) as (l1 & l2 & ->). destruct (in_split y extra Hy) as (e1 & e2 & ->).
exists (l1 ++ l2 ++ e1 ++ e2). eapply Permutation_trans; [exact HP|].
rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
rewrite (app_assoc l2 e1 (y :: e2)), (app_assoc l1 (l2 ++ e1) (y :: e2)).
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
rewrite <- !app_assoc. apply Permutation_refl.
Qed.

(* crt_INV_81fb8's two poison clauses: no head of U3 meets the input or `same`'s window. U3 is the entry's heads and
   text's head (crt_keepA); each entry head is the header of an entry block (fs_heads), so AR separates it from the
   fresh block `same` (the input it misses by crt_base's last conjunct); text's head is the header of the fresh text
   block, separated from the input's block by AR and from `same` by crt_keepA's own separation. *)
Lemma a23_U3_sep : forall cx same k ly3 S3 U3 (W3 : world tfibsegs) ms3 mem md,
  crt_base B cx -> ARU tfibsegs B ly3 S3 U3 W3 mem md -> crt_keepA B cx same k ly3 S3 U3 W3 ms3 ->
  Forall (fun q => c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= fst q \/ fst q + snd q <= c_t cx) U3 /\
  Forall (fun q => same + Z.of_nat (length (c_tb cx)) + 1 <= fst q \/ fst q + snd q <= same) U3.
Proof.
intros cx same k ly3 S3 U3 W3 ms3 mem md HB HARU HK.
destruct (a23_base_inblk cx HB) as (pt & kt & Hpt & Hpt1 & Hpt2).
pose proof (a23_base_ut cx HB) as HUT. rewrite Forall_forall in HUT.
pose proof HB as (_ & HHEADS & _).
destruct HK as (_ & _ & _ & KP & KU & _ & _ & _ & _ & Ks1 & Ks2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kd3 & _).
cbn zeta in KP, KU, Ks1, Ks2, Kd3.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 mem md HARU) as HAR.
assert (InL : forall x, In x (ablocks B (c_ly cx) (c_S cx)) -> In x (ablocks B ly3 S3))
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; left; exact Hx).
assert (Rk : req_size kt = kt) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec kt 0); lia).
assert (Rn : req_size (Z.of_nat (length (c_tb cx)) + 1) = Z.of_nat (length (c_tb cx)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (c_tb cx)) + 1) 0); lia).
assert (Re : req_size (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)
             = FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD).
{ unfold req_size, HEAD, FSH_Fn_writer.enc_size.
  pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)).
  destruct (Z.eqb_spec ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1 + 16) 0); lia. }
assert (HenP : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ unfold FSH_Fn_writer.enc_size. pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)).
  lia. }
split; apply Forall_forall; intros q Hq; apply (Permutation_in _ KU) in Hq; apply in_app_or in Hq;
  destruct Hq as [Hq | [<- | []]].
- exact (HUT q Hq).
- cbn [fst snd].
  destruct (a23_perm2 _ _ _ (pt, kt) _ KP Hpt (or_introl eq_refl)) as (rest & HP).
  pose proof (sep_blocks_perm tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md _ _ rest HAR HP) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Rk, Re in Hd. unfold HEAD in *. lia.
- destruct (HHEADS q Hq) as (Hsnd & m & Hm & Hm16).
  destruct (a23_perm2 _ _ _ (fst q, m) (same, Z.of_nat (length (c_tb cx)) + 1) KP Hm
    (or_intror (or_intror (or_introl eq_refl)))) as (rest & HP).
  pose proof (sep_blocks_perm tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md _ _ rest HAR HP) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Rn in Hd. lia.
- cbn [fst snd]. unfold HEAD in *. lia.
Qed.

(* a register the engine left as a closed literal term reads that literal's value *)
Ltac a23_litreg HS q :=
  match type of HS with st_ok _ ?E ?SS (restrict ?H ?M) =>
    let Y := fresh "Y" in
    pose proof (st_ok_restrict_reg tfibsegs H E SS M q HS) as Y; cbn [ms_regs restrict] in Y;
    rewrite Y; a23_srget; apply bv_eq; vm_compute; reflexivity end.

Lemma a23_seg6b :
  crt_from SK B (crt_ss_ret 0x8210c crt_cs1 crt_csF) (a23_and (crt_INV_81fb8 B) (crt_R7 B)) ->
  crt_from SK B (crt_ss_ret 0x820c4 crt_cs1e crt_csF) (a23_and a23_INV_78 (crt_R5 B)).
Proof.
intros NEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HINV as (HI78 & HR5).
destruct HI78 as (I10 & I18 & I27 & I25 & I22 & I19 & IZw & (same & HK)).
cbn zeta in I10, I18, I27, I25, I22, I19, IZw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HFO as (Hfrs & Hnin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfrs)
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in K20r, K21r, K24r, KP, KU, KH, K7, K8, K9, Ks1, Ks2, HX1, HX2, HI1, HI2, K12, K13, K14, K15,
  Kd1, Kd2, Kd3, Kd4, Kd5, Kp1, Kp2, Kwu, Ksh1, Ksh2.
(* the old boundary's register atoms and frame chunk, read before the run replaces HS *)
assert (O18 : YK11.getr (ms_regs ms3) 18%bv = ew E 18)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O20 : YK11.getr (ms_regs ms3) 20%bv = ew E 20)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O21 : YK11.getr (ms_regs ms3) 21%bv = ew E 21)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O19 : YK11.getr (ms_regs ms3) 19%bv = ew E 19)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O22 : YK11.getr (ms_regs ms3) 22%bv = ew E 22)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O24 : YK11.getr (ms_regs ms3) 24%bv = ew E 24)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O25 : YK11.getr (ms_regs ms3) 25%bv = ew E 25)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O27 : YK11.getr (ms_regs ms3) 27%bv = ew E 27)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (HCSF0 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_F cx)) crt_csF).
{ assert (H2r : nth_error (ss_mem (crt_ss_ret 0x820c4 crt_cs1e crt_csF)) 2 = Some (crt_frame_region crt_csF))
    by reflexivity.
  pose proof (fsw_region_nth E _ (restrict (w_H W3) ms3) 2 (crt_frame_region crt_csF) HS H2r) as HRF.
  destruct HRF as (_ & _ & _ & Hc). cbn [crt_frame_region YP09.r_base YP09.r_chunks base_val] in Hc.
  assert (EFv : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
  rewrite EFv in Hc. exact Hc. }
(* re-seat a0 on the s11 atom, so the engine decides `bne a0, s11` at 0x820c4, and s6 on F's extra atom 47, so the
   three slot stores 0x820d0 / 0x820e0 / 0x820e8 write crt_cs1's chunks (B only; A read F from slot 0x28) *)
pose proof (st_ok_submem tfibsegs E _ _ _ HS (a23_sub2 0x820c4 crt_cs1e crt_csF)
  ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (a23_ss2 0x820c4 crt_cs1e) (restrict (w_H W3) ms3)) in HS2.
assert (HS3a : st_ok tfibsegs E
  (mkSS (ss_pc (a23_ss2 0x820c4 crt_cs1e)) (sr_set (ss_regs (a23_ss2 0x820c4 crt_cs1e)) 10%bv (SOff 27 0))
     (ss_mem (a23_ss2 0x820c4 crt_cs1e)) (ss_resv (a23_ss2 0x820c4 crt_cs1e))
     (ss_facts (a23_ss2 0x820c4 crt_cs1e))) (restrict (w_H W3) ms3)).
{ apply (st_ok_set_reg tfibsegs E _ _ 10%bv (SOff 27 0) HS2).
  - intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
  - cbn [ms_regs restrict]. rewrite fsw_SOff0, <- O27, I27, <- I10. reflexivity. }
assert (HS3 : st_ok tfibsegs E
  (mkSS (ss_pc (a23_ss2 0x820c4 crt_cs1e))
     (sr_set (sr_set (ss_regs (a23_ss2 0x820c4 crt_cs1e)) 10%bv (SOff 27 0)) 22%bv (SOff 47 0))
     (ss_mem (a23_ss2 0x820c4 crt_cs1e)) (ss_resv (a23_ss2 0x820c4 crt_cs1e))
     (ss_facts (a23_ss2 0x820c4 crt_cs1e))) (restrict (w_H W3) ms3)).
{ apply (st_ok_set_reg tfibsegs E _ _ 22%bv (SOff 47 0) HS3a).
  - intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
  - cbn [ms_regs restrict]. rewrite fsw_SOff0, (crt_E_F cx E HE), I22. reflexivity. }
clear HS HS3a.
fsw_aj_run_toU crt_tbl_ok HS3 HJ HARU 0x8210c.
{ exact (a23_awr2 B cx E ly3 S3 crt_cs1e HB HE). }
(* the run writes only the three s1 slots, all above alloc_ceiling *)
assert (HSB : same_below (ms_mem ms3) (ms_mem ms) alloc_ceiling)
  by exact (a23_sb B cx E crt_cs1e _ _ HB HE HF).
assert (AVB : forall a, 0 <= a < alloc_ceiling ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) (ms_mem ms3) a)
  by (intros a Ha; exact (aview_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling a HSB Ha)).
assert (MBB : forall a, 0 <= a < alloc_ceiling ->
  mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) a)
  by (intros a Ha; exact (mbyte_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling a HSB Ha)).
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crt_csF).
{ rewrite Forall_forall in HCSF0 |- *. intros c Hc'.
  apply (chunk_ok_mbyte E (mrestrict (w_H W3) (ms_mem ms3))); [|exact (HCSF0 c Hc')].
  intros i Hi. unfold crt_csF in Hc'. destruct Hc' as [<-|[]]. cbn in Hi. cbn [YP09.c_off].
  rewrite crt_frame3. apply MBB. lia. }
(* the boundary at 0x8210c: the engine's slot region holds crt_cs1's chunks, reordered by the three stores *)
destruct (a23_reenter SK B cx E k ly3 S3 U3 W3 ms _ _ 0x8210c crt_cs1 _ HB HE HS3
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)
  ltac:(intros c Hc; cbn [In] in Hc |- *; unfold crt_cs1 in Hc; cbn [In] in Hc; tauto)
  ltac:(unfold crt_cs1; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
  ltac:(unfold crt_atom_chunks, crt_cs1; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | cbn; lia]|]);
        apply Forall_nil)
  ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  HCSF HJ HARU Hin3) as (HE' & HS').
(* the frame word survives *)
assert (HFO' : crt_frame_ok cx S3 W3 ms).
{ split; [exact Hfrs|]. split; [exact Hnin|]. rewrite <- Hflag. apply rdword_ext. intros i Hi.
  rewrite crt_frame3. apply AVB. lia. }
assert (N18 : YK11.getr (ms_regs ms) 18%bv = ew E 18)
  by (eapply crt_reg_atom; [exact HS3 | vm_compute; reflexivity]).
assert (N19 : YK11.getr (ms_regs ms) 19%bv = ew E 19)
  by (eapply crt_reg_atom; [exact HS3 | vm_compute; reflexivity]).
assert (N20 : YK11.getr (ms_regs ms) 20%bv = ew E 20)
  by (eapply crt_reg_atom; [exact HS3 | vm_compute; reflexivity]).
assert (N21 : YK11.getr (ms_regs ms) 21%bv = ew E 21)
  by (eapply crt_reg_atom; [exact HS3 | vm_compute; reflexivity]).
assert (N24 : YK11.getr (ms_regs ms) 24%bv = ew E 24)
  by (eapply crt_reg_atom; [exact HS3 | vm_compute; reflexivity]).
assert (N25 : YK11.getr (ms_regs ms) 25%bv = ew E 25)
  by (eapply crt_reg_atom; [exact HS3 | vm_compute; reflexivity]).
(* the registers the stretch 0x820c8 .. 0x82108 sets, read off the engine's answer *)
assert (EFv : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
assert (V47 : forall c : Z, 0 <= c -> crt_F cx + c < 2 ^ 64 -> sv_denot E (SOff 47 c) = w64 (crt_F cx + c)).
{ intros c Hc0 Hc1. rewrite denot_lit_U.
  rewrite (U_atom_off E 47 (crt_F cx) c ltac:(apply bv_eq; rewrite EFv; symmetry; apply wz; lia)
    ltac:(lia) ltac:(lia)). reflexivity. }
assert (E24 : ew E 24 = Z_to_bv 64 same) by (rewrite <- O24; exact K24r).
assert (E25 : ew E 25 = Z_to_bv 64 (c_t cx)) by (rewrite <- O25; exact I25).
assert (X11 : YK11.getr (ms_regs ms) 11%bv = w64 0) by a23_litreg HS3 (11%bv : bv 5).
assert (X14 : YK11.getr (ms_regs ms) 14%bv = w64 32) by a23_litreg HS3 (14%bv : bv 5).
assert (X15 : YK11.getr (ms_regs ms) 15%bv = w64 (2 ^ 64 - 1)) by a23_litreg HS3 (15%bv : bv 5).
assert (X16 : YK11.getr (ms_regs ms) 16%bv = w64 0x100002600) by a23_litreg HS3 (16%bv : bv 5).
(* a3 = s9 - 1 (0x820f4) and a2 = ~same (0x820f0 `not a2, s8`, the engine's SAlu ALU_XOR s8 (SLit (-1))) *)
assert (X13 : YK11.getr (ms_regs ms) 13%bv = w64 (c_t cx - 1)).
{ pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 13%bv HS3) as Y. cbn [ms_regs restrict] in Y.
  rewrite Y. a23_srget. rewrite denot_lit_U.
  rewrite (U_atom_off E 25 (c_t cx) (-1) E25 ltac:(lia) ltac:(lia)). reflexivity. }
assert (X12 : YK11.getr (ms_regs ms) 12%bv = w64 (2 ^ 64 - 1 - same)).
{ pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 12%bv HS3) as Y. cbn [ms_regs restrict] in Y.
  rewrite Y. a23_srget. rewrite denot_lit_U.
  rewrite (YI08.U_not E 24 same E24 ltac:(lia)). reflexivity. }
assert (X27 : YK11.getr (ms_regs ms) 27%bv = w64 (crt_F cx + 0xe0)).
{ pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 27%bv HS3) as Y. cbn [ms_regs restrict] in Y.
  rewrite Y. a23_srget. exact (V47 224 ltac:(lia) ltac:(lia)). }
assert (X23 : YK11.getr (ms_regs ms) 23%bv = w64 (crt_F cx + 0x80)).
{ pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 23%bv HS3) as Y. cbn [ms_regs restrict] in Y.
  rewrite Y. a23_srget. exact (V47 128 ltac:(lia) ltac:(lia)). }
assert (X22 : YK11.getr (ms_regs ms) 22%bv = w64 (crt_F cx + 0x1c0)).
{ pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 22%bv HS3) as Y. cbn [ms_regs restrict] in Y.
  rewrite Y. a23_srget. exact (V47 448 ltac:(lia) ltac:(lia)). }
(* crt_base's own facts about the input and its block *)
pose proof HB as HBc.
destruct HBc as (HPRE & HHEADS & HTOP & HFRL & HG10 & HG11 & HG12 & HZT & HTNZ & HTL & HWIN
  & (pt & kt & Hpt & Hpt1 & Hpt2) & HDEC & HBD & HZB & HRB & HSTAT & HQ & HLV & HRD & HSP47 & HNEV & HBB).
(* the blocks of the input and of `same`, in the CURRENT ablocks *)
assert (HinT : In (pt, kt) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; left; exact Hpt).
assert (HinS : In (same, Z.of_nat (length (c_tb cx)) + 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym KP)). apply in_or_app. right. cbn [In]. tauto. }
(* the memory facts, carried over the two slot stores (both above alloc_ceiling) *)
assert (HZT3 : zbytes_at tfibsegs W3 (ms_mem ms) (c_t cx) (HState.zs (c_tb cx ++ [Z_to_bv 8 0]))).
{ apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms))); [exact K9|].
  intros a Ha. apply MBB.
  assert (LI : Z.of_nat (length (HState.zs (c_tb cx ++ [Z_to_bv 8 0]))) = Z.of_nat (length (c_tb cx)) + 1)
    by (unfold HState.zs; rewrite length_map, length_app; cbn [length]; lia).
  rewrite LI in Ha. lia. }
assert (HZW3 : zbytes_at tfibsegs W3 (ms_mem ms) (c_want cx) (WriterSpec.b64_enc (c_bs cx) ++ [0])).
{ apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms))); [exact IZw|].
  intros a Ha. apply MBB.
  assert (LW : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx) ++ [0]))
               = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1)
    by (rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add, (check_round_trip_loops.enc_len_Z (c_bs cx));
        cbn [Z.of_nat]; lia).
  rewrite LW in Ha. pose proof (a23_want_lo B cx same k ly3 S3 U3 W3 ms3 _ _ HARU HK). lia. }
assert (HWS : forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
  writable_at tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a)
  by (intros a Ha; eapply writable_at_grows; [exact HG | exact (proj1 (K12 a Ha))]).
(* crt_keepA at the new state *)
assert (HK' : crt_keepA B cx same k ly3 S3 U3 W3 ms).
{ apply (a23_keepA_keep B cx same k ly3 S3 U3 W3 ms3 ms HF4096 HFceil).
  - intros a Ha Hr.
    pose proof (proj1 (a23_rd_facts B cx same k ly3 S3 U3 W3 ms3 HK a Hr)) as Hlow.
    apply a23_mb_of_raw. exact (HSB a ltac:(lia)).
  - exact HWS.
  - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]];
      [rewrite N20, O20 | rewrite N21, O21 | rewrite N24, O24]; reflexivity.
  - exact HK. }
(* the boundary invariant at 0x8210c and the frame predicate crt_R7 *)
assert (HIb8 : crt_INV_81fb8 B cx (Ereg (ms_regs ms) (crt_extra cx)) k ly3 S3 U3 W3 ms
  (with_vm_backing (m_vm_lazy md3) mat md3)).
{ cbn zeta. exists same.
  split; [rewrite N25, <- O25; exact I25|]. split; [exact X13|]. split; [exact X11|].
  split; [rewrite N24, <- O24; exact K24r|]. split; [rewrite N18, <- O18; exact I18|].
  split; [exact X14|]. split; [exact X16|]. split; [exact X12|]. split; [exact X15|].
  split; [exact HZT3|]. split; [exact Ks1|]. split; [exact Ks2|].
  split; [intros a Ha; split; [exact (HWS a Ha) | exact (proj2 (K12 a Ha))]|].
  split; [exists pt, kt; split; [exact HinT | split; [exact Hpt1 | exact Hpt2]]|].
  split; [exists same, (Z.of_nat (length (c_tb cx)) + 1); split; [exact HinS | split; lia]|].
  split; [exact Kd5|]. split; [exact HTNZ|].
  exact (a23_U3_sep cx same k ly3 S3 U3 W3 ms _ _ HB HARU HK'). }
assert (HR7 : crt_R7 B cx (Ereg (ms_regs ms) (crt_extra cx)) k ly3 S3 U3 W3 ms
  (with_vm_backing (m_vm_lazy md3) mat md3)).
{ exists same. split; [exact HK'|].
  split; [exact X27|]. split; [exact X23|]. split; [exact X22|].
  split; [rewrite N19, <- O19; exact I19 | exact HZW3]. }
exact (NEXT cx (Ereg (ms_regs ms) (crt_extra cx)) k ly3 S3 U3 W3 ms _ HB HE' HJ HARU HFO' (conj HIb8 HR7) HS').
Qed.
End seg6b.

(* a chunk list inside [lo, hi) of its base is kept by a memory that keeps those bytes *)
Lemma a23_chunks_mb : forall {fx : YK11.FPState} E (m m' : word -> option byte) base cs lo hi,
  Forall (fun c => lo <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  (forall a, base + lo <= a < base + hi -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m base) cs -> Forall (YP09.chunk_ok tfibsegs E m' base) cs.
Proof.
intros fx E m m' base cs lo hi Hin Hmb Hc. rewrite Forall_forall in Hin, Hc |- *. intros c Hc'.
apply (chunk_ok_mbyte E m); [|exact (Hc c Hc')].
intros i Hi. destruct (Hin c Hc') as (H1 & H2 & H3). apply Hmb. lia.
Qed.

(* ================= B 0x820a4 -> 0x820c4: the NUL store, its shadow check and the strlen thunk =================
   `sb zero, 0(a0)` at 0x820b4 writes want[En]; the ASan check 0x820a4 .. 0x820b0 reads that byte's shadow and the
   token engine takes the partial-granule slow path 0x82628 -> 0x820b4 itself, so __asan_report_store1 at 0x8262c is
   UNTAKEN (the deciding edge 0x820b0:bnez->0x82624). `beqz a0` at 0x820bc (text, `ld a0, 0x18(s1)`, atom 48) is
   decided by text's own atom fact. Then strlen (text) through the thunk at 0x820c0, whose result the guard at 0x820c4
   reads (A: 0x81f58 -> 0x81f78). ---- *)
Section seg6a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis IMG : fs_img_facts tfibsegs B.

Lemma a23_seg6a :
  crt_from SK B (crt_ss_ret 0x820c4 crt_cs1e crt_csF) (a23_and (a23_INV_78 B) (crt_R5 B)) ->
  crt_from SK B (crt_ss_ret 0x820a4 crt_cs1e crt_csF) (a23_and (crt_INV_81f58 B) (crt_R5 B)).
Proof.
intros NEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HINV as (HI58 & HR5).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
pose proof a23_STR as HSTR.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HFO as (Hfrs & Hnin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfrs)
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HI58 as HI58c.
destruct HI58c as (I10 & I18 & I27 & I22 & I19 & IZ & Iw1 & Iw2 & Ish & Iwin & IFd & IRA & IWR & IAW).
cbn zeta in I10, I18, I27, I22, I19, IZ, Iw1, Iw2, Ish, Iwin, IFd, IRA, IWR, IAW.
pose proof HR5 as HR5c.
destruct HR5c as (same & I25 & HK).
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in K20r, K21r, K24r, KP, KU, KH, K7, K8, K9, Ks1, Ks2, HX1, HX2, HI1, HI2, K12, K13, K14, K15,
  Kd1, Kd2, Kd3, Kd4, Kd5, Kp1, Kp2, Kwu, Ksh1, Ksh2.
(* text's block, which both the run's atom fact and the strlen contract need *)
assert (HinX : In (c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)
  (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym KP)). apply in_or_app. right. cbn [In]. tauto. }
assert (HTX1 : 4096 <= c_text cx) by (unfold HEAD in HX1; lia).
assert (HTX2 : c_text cx <= alloc_ceiling) by (unfold FSH_Fn_writer.enc_size in HX2; lia).
(* the old boundary's register atoms and frame chunk, read before the run replaces HS *)
assert (O18 : YK11.getr (ms_regs ms3) 18%bv = ew E 18)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O20 : YK11.getr (ms_regs ms3) 20%bv = ew E 20)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O21 : YK11.getr (ms_regs ms3) 21%bv = ew E 21)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O19 : YK11.getr (ms_regs ms3) 19%bv = ew E 19)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O22 : YK11.getr (ms_regs ms3) 22%bv = ew E 22)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O27 : YK11.getr (ms_regs ms3) 27%bv = ew E 27)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O24 : YK11.getr (ms_regs ms3) 24%bv = ew E 24)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (O25 : YK11.getr (ms_regs ms3) 25%bv = ew E 25)
  by (eapply crt_reg_atom; [exact HS | vm_compute; reflexivity]).
assert (HCSF0 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_F cx)) crt_csF).
{ assert (H2r : nth_error (ss_mem (crt_ss_ret 0x820a4 crt_cs1e crt_csF)) 2 = Some (crt_frame_region crt_csF))
    by reflexivity.
  pose proof (fsw_region_nth E _ (restrict (w_H W3) ms3) 2 (crt_frame_region crt_csF) HS H2r) as HRF.
  destruct HRF as (_ & _ & _ & Hc). cbn [crt_frame_region YP09.r_base YP09.r_chunks base_val] in Hc.
  assert (EFv : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
  rewrite EFv in Hc. exact Hc. }
assert (HSV0 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (spZ (c_regs cx))) crt_sv_chunks).
{ pose proof (fsw_region_nth E _ (restrict (w_H W3) ms3) 0 crt_s0_region HS ltac:(reflexivity)) as HR0.
  destruct HR0 as (_ & _ & _ & Hc).
  cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hc.
  pose proof HE as (E2 & _ & _ & E8 & _). rewrite E8 in Hc. exact Hc. }
assert (HC10 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_sp1 cx)) crt_cs1e).
{ pose proof (fsw_region_nth E _ (restrict (w_H W3) ms3) 1 (crt_slot_region crt_cs1e) HS ltac:(reflexivity)) as HR1.
  destruct HR1 as (_ & _ & _ & Hc). cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val] in Hc.
  pose proof HE as (_ & _ & _ & _ & E9 & _). rewrite E9 in Hc. exact Hc. }
(* the run state and its one shadow entry *)
assert (EV10 : bv_unsigned (ew E 10) = c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4).
{ rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 10%bv 10 HS ltac:(vm_compute; reflexivity)), I10.
  unfold w64. apply wz. lia. }
destruct (a23_st58 B cx E k ly3 S3 U3 W3 ms3 md3 HB HE HI58 HTX1 HTX2 HS) as (HS1 & SHOK).
clear HS.
fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK fs_Bspan PC_strlen.
{ (* the write set: the store's own byte, then the s0 words and the s1 slots *)
  eapply (awr_ok_cons_gen tfibsegs B E (a23_wr 10) _ _ _ _ _ _ _ _ _ 10%nat
    (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) ltac:(reflexivity) EV10).
  - intros a Ha. cbn [a23_wr YP09.r_wlo YP09.r_whi] in Ha.
    replace a with (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) by lia. exact IAW.
  - exact (a23_awr2 B cx E ly3 S3 crt_cs1e HB HE). }
(* the store's byte is the only memory the run moved below the ceiling *)
assert (HSBX : forall a, 0 <= a < alloc_ceiling -> a <> c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 ->
  ms_mem ms (Z_to_bv 64 a) = ms_mem ms3 (Z_to_bv 64 a)).
{ intros a Ha Hne. apply HF. rewrite (wz a ltac:(lia)). intros (rg & Hin & Hrg). cbn [In] in Hin.
  pose proof HE as (E2 & _ & _ & E8 & E9 & _).
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [a23_wr crt_s0_region fs_ret_s0_region crt_slot_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    [rewrite EV10 in Hrg | rewrite E8 in Hrg | rewrite E9 in Hrg]; lia. }
assert (MBX : forall a, 0 <= a < alloc_ceiling -> a <> c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 ->
  mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) a).
{ intros a Ha Hne. unfold mbyte, mrestrict.
  destruct (w_H W3 (Z_to_bv 64 a)); [reflexivity | rewrite (HSBX a Ha Hne); reflexivity]. }
(* text's bytes and its C string at the post-run memory *)
assert (LT : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx) ++ [0]))
  = FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, (check_round_trip_loops.enc_len_Z (c_bs cx)).
  unfold FSH_Fn_writer.enc_size. cbn [Z.of_nat]. lia. }
assert (LT' : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx) ++ [0]))
  = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1).
{ rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, (check_round_trip_loops.enc_len_Z (c_bs cx)).
  cbn [Z.of_nat]. lia. }
assert (HTa : 4112 <= c_text cx) by (unfold HEAD in HX1; lia).
assert (HTb : c_text cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1 <= alloc_ceiling)
  by (unfold FSH_Fn_writer.enc_size in HX2; lia).
assert (HTd : c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1 <= c_text cx - 16 \/
              c_text cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1 <= c_want cx)
  by (unfold HEAD, FSH_Fn_writer.enc_size in Kd2; lia).
assert (HZX : zbytes_at tfibsegs W3 (ms_mem ms) (c_text cx) (WriterSpec.b64_enc (c_bs cx) ++ [0])).
{ apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms))); [exact K8|].
  intros a Ha. rewrite LT' in Ha. apply MBX; lia. }
assert (HBO : WriterSpec.bytes_ok (c_bs cx)).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDEC & _).
  exact (WriterSpecFacts.b64_dec_ok _ _ HDEC). }
assert (HNZ : ~ In 0 (WriterSpec.b64_enc (c_bs cx))) by exact (crt_enc_nz (c_bs cx) HBO).
assert (HCS : cstr_ok tfibsegs W3 (ms_mem ms) (c_text cx) (WriterSpec.b64_enc (c_bs cx))).
{ apply (crt_cstr_of_rblock B ly3 S3 U3 W3 (ms_mem ms) _ (c_text cx) (WriterSpec.b64_enc (c_bs cx))
    (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) HARU KH HinX (proj1 (proj2 K7)));
  [ rewrite (check_round_trip_loops.enc_len_Z (c_bs cx)); unfold FSH_Fn_writer.enc_size; lia
  | exact HZX | exact HNZ ]. }
(* the env atom the call reads is text's; the token run's fresh atoms start at 51 (a23_tok58's atom-50 fact) *)
match type of HS1 with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
assert (HAG : env_agree 51 E E1).
{ unfold E1. split; [intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity | rewrite ?ed_ewset; reflexivity]. }
assert (EV48 : bv_unsigned (ew E1 48) = c_text cx).
{ rewrite (proj1 HAG 48%nat ltac:(lia)), (crt_E_text cx E HE). apply wz. lia. }
(* the strlen crossing *)
assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 PC_strlen) (ms_mem ms) (seg_rom tfibsegs))
  by (apply (crt_mkst (w_H W3) _ _ ms HS1); reflexivity).
rewrite Ems in HS1 |- *.
refine (crt_rt_call SK B _ 0x820c4 48%nat cx E1 k ly3 S3 U3 W3 _ (ms_mem ms) _
  (WriterSpec.b64_enc (c_bs cx)) _ RT IMG HB (a23_E_agree cx E _ HAG HE)
  _ _ _ _ _ _ _ HS1 _ HJ HARU _).
- vm_compute; reflexivity.
- lia.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- rewrite EV48. exact HCS.
- intros regs2 mem2 md2 HJ2 HARU2 HP2 Hv2 Hfr2 Hgr2.
  (* the boundary at 0x820c4: the registers the callee keeps, read off the run's atoms *)
  assert (RQ : forall (q : bv 5) (z : Z), q = Z_to_bv 5 z -> acallee_saved z ->
    YK11.getr regs2 q = YK11.getr (ms_regs ms) q) by (intros q z -> Hz; exact (HP2 z Hz)).
  Ltac a23_at HS HAG q n :=
    match type of HS with st_ok _ _ ?SS (restrict _ ?M) =>
      let X := fresh "X" in
      pose proof (crt_reg_atom _ _ M SS q n HS ltac:(vm_compute; reflexivity)) as X;
      cbn [ms_regs mkst] in X; rewrite X; apply (proj1 HAG); lia end.
  assert (A2 : YK11.getr (ms_regs ms) 2%bv = ew E 2) by a23_at HS1 HAG (2%bv : bv 5) 2%nat.
  assert (A3 : YK11.getr (ms_regs ms) 3%bv = ew E 3) by a23_at HS1 HAG (3%bv : bv 5) 3%nat.
  assert (A4 : YK11.getr (ms_regs ms) 4%bv = ew E 4) by a23_at HS1 HAG (4%bv : bv 5) 4%nat.
  assert (A8 : YK11.getr (ms_regs ms) 8%bv = ew E 8) by a23_at HS1 HAG (8%bv : bv 5) 8%nat.
  assert (A9 : YK11.getr (ms_regs ms) 9%bv = ew E 9) by a23_at HS1 HAG (9%bv : bv 5) 9%nat.
  assert (A26 : YK11.getr (ms_regs ms) 26%bv = ew E 26) by a23_at HS1 HAG (26%bv : bv 5) 26%nat.
  assert (A19 : YK11.getr (ms_regs ms) 19%bv = ew E 19) by a23_at HS1 HAG (19%bv : bv 5) 19%nat.
  assert (A27 : YK11.getr (ms_regs ms) 27%bv = ew E 27) by a23_at HS1 HAG (27%bv : bv 5) 27%nat.
  assert (A18 : YK11.getr (ms_regs ms) 18%bv = ew E 32) by a23_at HS1 HAG (18%bv : bv 5) 32%nat.
  assert (A20 : YK11.getr (ms_regs ms) 20%bv = ew E 20) by a23_at HS1 HAG (20%bv : bv 5) 20%nat.
  assert (A21 : YK11.getr (ms_regs ms) 21%bv = ew E 21) by a23_at HS1 HAG (21%bv : bv 5) 21%nat.
  assert (A22 : YK11.getr (ms_regs ms) 22%bv = ew E 22) by a23_at HS1 HAG (22%bv : bv 5) 22%nat.
  assert (A24 : YK11.getr (ms_regs ms) 24%bv = ew E 24) by a23_at HS1 HAG (24%bv : bv 5) 24%nat.
  assert (A25 : YK11.getr (ms_regs ms) 25%bv = ew E 25) by a23_at HS1 HAG (25%bv : bv 5) 25%nat.
  assert (K : forall (q : bv 5) (z : Z), q = Z_to_bv 5 z -> acallee_saved z ->
    YK11.getr regs2 q = YK11.getr (ms_regs ms) q) by exact RQ.
  assert (CS : forall z, (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ (18 <= z <= 27)) -> acallee_saved z)
    by (intros z Hz; exact Hz).
  pose proof HE as (E2v & E3v & E4v & E8v & E9v & E26v & EXv).
  assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
    by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
  assert (G2 : YK11.getr regs2 2%bv = Z_to_bv 64 (crt_sp1 cx))
    by exact (eq_trans (K 2%bv 2 eq_refl ltac:(apply CS; lia)) (eq_trans A2 (V 2%nat _ E2v ltac:(lia)))).
  assert (G3 : YK11.getr regs2 3%bv = YK11.getr (c_regs cx) 3%bv)
    by exact (eq_trans (K 3%bv 3 eq_refl ltac:(apply CS; lia)) (eq_trans A3 E3v)).
  assert (G4 : YK11.getr regs2 4%bv = YK11.getr (c_regs cx) 4%bv)
    by exact (eq_trans (K 4%bv 4 eq_refl ltac:(apply CS; lia)) (eq_trans A4 E4v)).
  assert (G8 : YK11.getr regs2 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
    by exact (eq_trans (K 8%bv 8 eq_refl ltac:(apply CS; lia))
                (eq_trans A8 (V 8%nat _ E8v ltac:(unfold spZ; apply u64_range)))).
  assert (G9 : YK11.getr regs2 9%bv = Z_to_bv 64 (crt_sp1 cx))
    by exact (eq_trans (K 9%bv 9 eq_refl ltac:(apply CS; lia)) (eq_trans A9 (V 9%nat _ E9v ltac:(lia)))).
  assert (G26 : YK11.getr regs2 26%bv = Z_to_bv 64 (crt_SF cx))
    by exact (eq_trans (K 26%bv 26 eq_refl ltac:(apply CS; lia))
                (eq_trans A26 (V 26%nat _ E26v ltac:(pose proof (u64_range (ew E 26)); lia)))).
  (* the memory: the callee keeps everything outside its stack window, the run everything below the ceiling but
     the store's byte *)
  assert (MBS : forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx) ->
    mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a)
    by (intros a Ha Hn; exact (mbyte_of_aview tfibsegs (w_H W3) (w_H W3) (ms_mem ms) mem2 a (Hfr2 a Ha Hn))).
  assert (MB2 : forall a, 0 <= a < alloc_ceiling ->
    mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a)
    by (intros a Ha; apply MBS; lia).
  assert (MB3 : forall a, 0 <= a < alloc_ceiling -> a <> c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 ->
    mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) a)
    by (intros a Ha Hne; rewrite (MB2 a Ha); exact (MBX a Ha Hne)).
  assert (AV3 : forall a, 0 <= a < alloc_ceiling -> a <> c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 ->
    aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) (ms_mem ms3) a)
    by (intros a Ha Hne; unfold aview; rewrite (MB3 a Ha Hne); reflexivity).
  (* the chunks the boundary at 0x820c4 holds, at the returned memory and under the run's env *)
  assert (HE1 : crt_E cx E1) by exact (a23_E_agree cx E E1 HAG HE).
  assert (E8w : bv_unsigned (ew E1 8) = spZ (c_regs cx)) by (rewrite (proj1 HAG 8%nat ltac:(lia)); exact E8v).
  assert (E9w : bv_unsigned (ew E1 9) = crt_sp1 cx) by (rewrite (proj1 HAG 9%nat ltac:(lia)); exact E9v).
  assert (HSV2 : Forall (YP09.chunk_ok tfibsegs E1 (mrestrict (w_H W3) mem2) (spZ (c_regs cx))) crt_sv_chunks).
  { pose proof (fsw_region_nth E1 _ _ 1 crt_s0_region HS1 eq_refl) as (_ & _ & _ & Hc).
    cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val ms_mem mkst] in Hc. rewrite E8w in Hc.
    apply (a23_chunks_mb E1 (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) mem2) _ _ (-104) 0); [| | exact Hc].
    - rewrite Forall_forall. intros c Hc'. pose proof (proj1 (Forall_forall _ _) crt_sv_in c Hc') as (X1 & X2).
      unfold crt_sv_chunks in Hc'. cbn [seq map In] in Hc'.
      repeat (destruct Hc' as [<-|Hc']; [cbn; lia|]). destruct Hc'.
    - intros a Ha. apply MBS; lia. }
  assert (HCS2 : Forall (YP09.chunk_ok tfibsegs E1 (mrestrict (w_H W3) mem2) (crt_sp1 cx)) crt_cs1e).
  { pose proof (fsw_region_nth E1 _ _ 2 (crt_slot_region crt_cs1e) HS1 eq_refl) as (_ & _ & _ & Hc).
    cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val ms_mem mkst] in Hc. rewrite E9w in Hc.
    apply (a23_chunks_mb E1 (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) mem2) _ _ 0x10 0x58); [| | exact Hc].
    - unfold crt_cs1e. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - intros a Ha. apply MBS; lia. }
  assert (HCSF2 : Forall (YP09.chunk_ok tfibsegs E1 (mrestrict (w_H W3) mem2) (crt_F cx)) crt_csF).
  { apply (crt_chunks_env E E1); [intros n Hn; apply (proj1 HAG); lia
      | unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]|].
    apply (a23_chunks_mb E (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) mem2) _ _ 504 512); [| | exact HCSF0].
    - unfold crt_csF. rewrite crt_frame3. apply Forall_cons; [cbn; lia | apply Forall_nil].
    - intros a Ha. apply MB3; [lia|]. rewrite crt_frame3 in IFd. destruct IFd as [Hd|Hd]; lia. }
  destruct (a23_reseat SK B cx E1 k ly3 S3 U3 W3 regs2 mem2 md2 0x820c4 crt_cs1e crt_csF
    HE1 H16 H0 Hceil0 H47 HJ2 HARU2 Hin3 G2 G3 G4 G8 G9 G26 HSV2 HCS2 HCSF2
    ltac:(unfold crt_cs1e; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
    ltac:(unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil])
    ltac:(unfold crt_atom_chunks, crt_cs1e; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | cbn; lia]|]);
          apply Forall_nil)
    ltac:(unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil])
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (HE' & HS').
  (* the NUL the store wrote at want + En, read off the run's store region and carried over the call *)
  assert (EV10' : bv_unsigned (ew E1 10) = c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
    by (rewrite (proj1 HAG 10%nat ltac:(lia)); exact EV10).
  assert (HNUL : val_mem tfibsegs (mrestrict (w_H W3) mem2)
    (c_want cx + Z.of_nat (length (WriterSpec.b64_enc (c_bs cx)))) 1 0).
  { pose proof (fsw_region_nth E1 _ _ 0 (YP09.mkRegion (Some 10%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
      HS1 eq_refl) as (_ & _ & _ & Hc).
    cbn [YP09.r_base YP09.r_chunks base_val ms_mem mkst] in Hc. rewrite EV10' in Hc.
    pose proof (proj1 (Forall_forall _ _) Hc _ (or_introl eq_refl) 0 ltac:(cbn; lia)) as (b & Hb & Hm).
    intros kk Hk. destruct kk as [|kk]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite (check_round_trip_loops.enc_len_Z (c_bs cx)).
    rewrite (MB2 (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) ltac:(lia)).
    cbn [YP09.c_off ms_mem restrict mkst] in Hm. rewrite !Z.add_0_r in Hm. rewrite Hm. f_equal.
    cbn in Hb. injection Hb as <-. apply bv_eq. vm_compute. reflexivity. }
  assert (HZW2 : zbytes_at tfibsegs W3 mem2 (c_want cx) (WriterSpec.b64_enc (c_bs cx) ++ [0])).
  { apply (garr8_app1 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) mem2) (c_want cx)
      (WriterSpec.b64_enc (c_bs cx)) 0 IZ HNUL ltac:(lia)).
    intros a Ha. rewrite (check_round_trip_loops.enc_len_Z (c_bs cx)) in Ha. apply MB3; lia. }
  (* the inner boundary invariant and the frame predicate at 0x820c4 *)
  assert (HK2 : crt_keepA B cx same k ly3 S3 U3 W3 (mkst regs2 (Z_to_bv 64 0x820c4) mem2 (seg_rom tfibsegs))).
  { apply (a23_keepA_keep B cx same k ly3 S3 U3 W3 ms3 _ HF4096 HFceil).
    - intros a Ha Hr. cbn [ms_mem mkst].
      destruct (a23_rd_facts B cx same k ly3 S3 U3 W3 ms3 HK a Hr) as (F1 & F2 & _).
      apply MB3; [exact F1 | exact F2].
    - intros a Ha. cbn [ms_mem mkst]. apply (apresent_writable tfibsegs). apply Hgr2.
      apply (YE7f.apresent_of_writable (w_H W3) (ms_mem ms) a);
        [lia | apply a23_not_img; destruct Kp2 as [Hd|Hd]; unfold FS_IMG_END in *; lia|].
      eapply writable_at_grows; [exact HG | exact (proj1 (K12 a Ha))].
    - intros r Hr. cbn [ms_regs mkst]. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]].
      + exact (eq_trans (K 20%bv 20 eq_refl ltac:(apply CS; lia)) (eq_trans A20 (eq_sym O20))).
      + exact (eq_trans (K 21%bv 21 eq_refl ltac:(apply CS; lia)) (eq_trans A21 (eq_sym O21))).
      + exact (eq_trans (K 24%bv 24 eq_refl ltac:(apply CS; lia)) (eq_trans A24 (eq_sym O24))).
    - exact HK. }
  assert (R25 : YK11.getr regs2 25%bv = w64 (c_t cx))
    by exact (eq_trans (K 25%bv 25 eq_refl ltac:(apply CS; lia)) (eq_trans A25 (eq_trans (eq_sym O25) I25))).
  assert (HI78 : a23_INV_78 B cx (Ereg regs2 (crt_extra cx)) k ly3 S3 U3 W3
    (mkst regs2 (Z_to_bv 64 0x820c4) mem2 (seg_rom tfibsegs)) md2).
  { unfold a23_INV_78. cbn zeta. cbn [ms_regs ms_mem mkst].
    split; [rewrite Hv2, (check_round_trip_loops.enc_len_Z (c_bs cx)); reflexivity|].
    split; [exact (eq_trans (K 18%bv 18 eq_refl ltac:(apply CS; lia)) (eq_trans A18 (crt_E_shadow cx E HE)))|].
    split; [exact (eq_trans (K 27%bv 27 eq_refl ltac:(apply CS; lia)) (eq_trans A27 (eq_trans (eq_sym O27) I27)))|].
    split; [exact R25|].
    split; [exact (eq_trans (K 22%bv 22 eq_refl ltac:(apply CS; lia)) (eq_trans A22 (eq_trans (eq_sym O22) I22)))|].
    split; [exact (eq_trans (K 19%bv 19 eq_refl ltac:(apply CS; lia)) (eq_trans A19 (eq_trans (eq_sym O19) I19)))|].
    split; [exact HZW2|]. exists same. exact HK2. }
  assert (HR5' : crt_R5 B cx (Ereg regs2 (crt_extra cx)) k ly3 S3 U3 W3
    (mkst regs2 (Z_to_bv 64 0x820c4) mem2 (seg_rom tfibsegs)) md2)
    by (exists same; split; [exact R25 | exact HK2]).
  assert (HFO' : crt_frame_ok cx S3 W3 (mkst regs2 (Z_to_bv 64 0x820c4) mem2 (seg_rom tfibsegs))).
  { split; [exact Hfrs|]. split; [exact Hnin|]. rewrite <- Hflag. apply rdword_ext. intros i Hi.
    cbn [ms_mem mkst]. rewrite crt_frame3. rewrite crt_frame3 in IFd. apply AV3; [lia|].
    destruct IFd as [Hd|Hd]; lia. }
  exact (NEXT cx (Ereg regs2 (crt_extra cx)) k ly3 S3 U3 W3 (mkst regs2 (Z_to_bv 64 0x820c4) mem2 (seg_rom tfibsegs))
    md2 HB HE' HJ2 HARU2 HFO' (conj HI78 HR5') HS').
Qed.
End seg6a.

(* ================= segment 6, B 0x820a4 -> 0x8210c: the from-lemma of this lane's first piece ================= *)
Section seg6c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Lemma a23_seg6 :
  crt_from SK B (crt_ss_ret 0x8210c crt_cs1 crt_csF) (a23_and (crt_INV_81fb8 B) (crt_R7 B)) ->
  crt_from SK B (crt_ss_ret 0x820a4 crt_cs1e crt_csF) (a23_and (crt_INV_81f58 B) (crt_R5 B)).
Proof. intros H. exact (a23_seg6a SK B RT IMG (a23_seg6b SK B H)). Qed.
End seg6c.

(* ================= segments 8-9's string facts: `same` and `want` are blocks with no head of their own =========
   Text's block carries a 16-byte head (fuzz/alloc.c), so FSH_crt_cstr's builders ask the string to start past it.
   `same` and `want` are ASan blocks listed at their own address: their first bytes are body. What makes a block range
   addressable on the machine's memory is that no user-poisoned head meets it; for these two blocks crt_keepA's
   separations and AR give that directly. ---- *)
Section blk0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* a block range no head of U meets is addressable on the machine's memory (FSW_rd.fsw_block_body_addressable with
   the head premise `P + 16 <= z` replaced by the U-miss premise) *)
Lemma a23_block_addr_noU : forall ly S U (W : world tfibsegs) mem md P n z len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (P, n) (ablocks B ly S) -> P <= z -> 0 <= len -> z + len <= P + req_size n ->
  (forall q, In q U -> fst q + snd q <= z \/ z + len <= fst q) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF z len.
Proof.
intros ly S U W mem md P n z len HARU FH Hin Hz Hl Hn HU.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (YCbq.range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P n z len HAR Hin Hz Hn)
  as HRA.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as (HP16 & HP4096 & HPc & _).
pose proof asan_consts as (C1 & _).
intros x Hx. destruct (HRA x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (NI : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
{ rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply fsw_head_ush_out; [lia|]. intros (h & q) Hr. cbn [fst snd].
  destruct (FH (h, q) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in E16, Hm. subst q.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hm) as (Hh16 & _).
  split; [reflexivity|].
  split; [apply Z.mod_divide in Hh16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((k * 2) * 8) by lia;
          apply Z_mod_mult|].
  pose proof (HU (h, 16) Hr) as Hd. cbn [fst snd] in Hd. lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ NI). exact Es.
Qed.

(* a string inside a live block that no head of U meets is cstr_ok on the machine's memory (FSH_crt_cstr's
   crt_cstr_of_block with `b + HEAD <= p` replaced by `b <= p` and the U-miss premise) *)
Lemma a23_cstr_of_block0 : forall ly S U (W : world tfibsegs) mem md p (l : list Z) b m,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, m) (ablocks B ly S) -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall q, In q U -> fst q + snd q <= p \/ p + Z.of_nat (length l) + 1 <= fst q) ->
  zbytes_at tfibsegs W mem p (l ++ [0]) -> ~ In 0 l ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S U W mem md p l b m HARU FH Hin Hb Hbm HU Hz Hnz.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HARU as (_ & _ & PO).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR Hin) as (_ & H4096 & Hc & Happ & _ & _ & Hmax).
unfold MALLOC_MAX in Hmax.
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite Hrq in Hc, Happ.
pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as HCV.
split; [split; [exact Hz|]|].
{ apply Forall_forall. intros c Hc0 E. subst c. exact (Hnz Hc0). }
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; lia. }
split.
{ apply (a23_block_addr_noU ly S U W mem md b m p (Z.of_nat (length l) + 1) HARU FH Hin); [lia | lia | rewrite Hrq; lia |].
  intros q Hq. rewrite Z.add_assoc. exact (HU q Hq). }
split.
{ destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md b m HAR Hin) as (_ & Hhv). rewrite Hrq in Hhv.
  intros s Hs. eapply aview_unpoison_vis; [exact PO|].
  exact (shadow_hull_vis_sub _ b m p (Z.of_nat (length l) + 1) Hhv ltac:(lia) ltac:(lia) ltac:(lia) s Hs). }
intros a Ha. eapply aview_unpoison_vis; [exact PO|].
apply (block_word_tail_vis B ly S W (unpoison U mem) md b m HAR Hin Hm).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.
End blk0.

(* ================= segments 8-9's run states =================
   B 0x82180 -> PC_strcmp: the UBSan pointer-overflow test `bltu a2, a1` at 0x82180 (a2 = ~same, atom 12, a1 = |strip|,
   atom 11; its trap arm 0x82620 `unimp` UNTAKEN by the two atom facts), the NUL store `sb zero, 0(a0)` at 0x8219c at
   a0 = same + |strip| (atom 51 = crt_xatom 0, a fresh env atom the run's alias facts name as s8 + a1; A: atom 50 =
   s8 + a2), its ASan check (the slow path 0x82630 -> 0x82198, so __asan_report_store1 at 0x82638 is UNTAKEN),
   `ld s2, 0x18(s1)` (text), and the `n mod 4` branch 0x821a4, decided by the case condition on atom 11: taken
   (|strip| mod 4 <> 0) it goes straight to the second strcmp at 0x821c0 (ra = 0x821c4); not taken, to the first at
   0x821b0 (ra = 0x821b4). 0x821b4 -> PC_strcmp: after the first strcmp returned 0, `bnez a0` at 0x821b4 (the abort
   arm 0x824e4 UNTAKEN), `ld a1, 0x30(s1)` (want), the second strcmp. ---- *)
Definition a23_nsm : afact := mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1 - 4096) 0.
Definition a23_base28 : sstate :=
  mkSS 0x82180 (sr_set sr_atoms 18%bv (SOff 32 0)) (a23_wr 51 :: [crt_s0_region; crt_slot_region crt_cs1]) None
    (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] []).
Definition a23_tok28 (c : branch_cond) : sstate :=
  add_cond (add_alias (add_alias (add_atom (add_atom (add_atom (add_atom (add_atom (add_atom a23_base28
    48%nat a23_af) 11%nat (mkAF 0 3145728 0)) 24%nat a23_af) 51%nat a23_af) 32%nat a23_shb) 12%nat a23_nsm)
    (SAlu ALU_ADD (SOff 11 0) (SOff 24 0)) (SOff 51 0)) (SAlu ALU_ADD (SOff 24 0) (SOff 11 0)) (SOff 51 0))
    (mkAC c (SAlu ALU_AND (SOff 11 0) (SLit 3)) (SLit 0)).
Definition a23_SH28 : list shent := [mkSHE 51 0 1].
Definition a23_base2858 : sstate :=
  mkSS 0x821b4 (sr_set sr_atoms 10%bv (SLit 0)) [crt_s0_region; crt_slot_region crt_cs1] None
    (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] []).

Section seg89h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma a23_strip_len : forall l, (length (B64Canon.b64_strip l) <= length l)%nat.
Proof.
intros l. unfold B64Canon.b64_strip. induction l as [|c l IH].
- simpl. lia.
- simpl. destruct (negb (b64_ws c)); simpl; lia.
Qed.
Lemma a23_zs_len : forall tb, length (HState.zs tb) = length tb.
Proof. intros tb. unfold HState.zs. apply length_map. Qed.

(* no head of U3 meets `want`'s or `same`'s block: the entry heads are headers of entry blocks, which AR separates from
   the two fresh blocks; text's head by the given separation *)
Lemma a23_U3_fresh : forall cx same k ly3 S3 U3 (W3 : world tfibsegs) ms3 mem md b m,
  crt_base B cx -> ARU tfibsegs B ly3 S3 U3 W3 mem md -> crt_keepA B cx same k ly3 S3 U3 W3 ms3 ->
  In (b, m) [(c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1); (same, Z.of_nat (length (c_tb cx)) + 1)] ->
  (b + m <= c_text cx - HEAD \/ c_text cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) <= b) ->
  forall q, In q U3 -> fst q + snd q <= b \/ b + m <= fst q.
Proof.
intros cx same k ly3 S3 U3 W3 ms3 mem md b m HB HARU HK Hbm Hsep q Hq.
pose proof HB as (_ & HHEADS & _).
destruct HK as (_ & _ & _ & KP & KU & _). cbn zeta in KP, KU.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 mem md HARU) as HAR.
assert (Hm0 : 0 < m).
{ cbn [In] in Hbm. destruct Hbm as [E|[E|[]]]; injection E as <- <-; [|lia].
  pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)). lia. }
assert (Rm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (HenP : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ unfold FSH_Fn_writer.enc_size. pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)).
  lia. }
apply (Permutation_in _ KU) in Hq. apply in_app_or in Hq. destruct Hq as [Hq | [<- | []]].
- destruct (HHEADS q Hq) as (Hsnd & m' & Hm' & Hm16).
  destruct (a23_perm2 _ _ _ (fst q, m') (b, m) KP Hm' (or_intror Hbm)) as (rest & HP).
  pose proof (sep_blocks_perm tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md _ _ rest HAR HP) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Rm in Hd. lia.
- cbn [fst snd]. unfold HEAD in *. lia.
Qed.

(* the memory bundle segments 8-9 carry from B 0x82180 to the second strcmp: crt_keepA, `want`'s string, `same`'s
   string with its NUL, and the frame's flag word, all below alloc_ceiling *)
Lemma a23_D_keep : forall cx same k ly3 S3 U3 (W3 : world tfibsegs) (ms ms' : machine_state),
  0 <= crt_F cx -> crt_F cx + 512 <= alloc_ceiling ->
  (forall a, 0 <= a < alloc_ceiling ->
     mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms')) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a) ->
  (forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
     writable_at tfibsegs (mrestrict (w_H W3) (ms_mem ms')) a) ->
  (forall r : bv 5, In r [20; 21; 24]%bv -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r) ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms ->
  zbytes_at tfibsegs W3 (ms_mem ms) (c_want cx) (WriterSpec.b64_enc (c_bs cx) ++ [0]) ->
  zbytes_at tfibsegs W3 (ms_mem ms) same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) ->
  crt_frame_ok cx S3 W3 ms ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms' /\
  zbytes_at tfibsegs W3 (ms_mem ms') (c_want cx) (WriterSpec.b64_enc (c_bs cx) ++ [0]) /\
  zbytes_at tfibsegs W3 (ms_mem ms') same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) /\
  crt_frame_ok cx S3 W3 ms'.
Proof.
intros cx same k ly3 S3 U3 W3 ms ms' HF0 HFc HM HW HR HK HZW HZS HFO.
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof HK as HK'.
destruct HK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kp1 & Kp2 & Kwlo & Kwu & _).
cbn zeta in Ks1, Ks2, HX1, HX2, HI1, HI2, Kp1, Kp2, Kwu.
pose proof (a23_strip_len (HState.zs (c_tb cx))) as SL. rewrite a23_zs_len in SL.
split.
{ apply (a23_keepA_keep B cx same k ly3 S3 U3 W3 ms ms' KF1 KF2); [|exact HW | exact HR | exact HK].
  intros a Ha Hr. apply HM. exact (proj1 (a23_rd_facts B cx same k ly3 S3 U3 W3 ms HK a Hr)). }
split.
{ apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) (ms_mem ms'))); [exact HZW|].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  rewrite Nat2Z.inj_add, (check_round_trip_loops.enc_len_Z (c_bs cx)) in Ha. apply HM. cbn [Z.of_nat] in Ha. lia. }
split.
{ apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) (ms_mem ms'))); [exact HZS|].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite Nat2Z.inj_add in Ha. apply HM.
  cbn [Z.of_nat] in Ha. lia. }
destruct HFO as (Hfrs & Hnin & Hflag). split; [exact Hfrs|]. split; [exact Hnin|].
rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3.
unfold aview. rewrite (HM (crt_F cx + 512 - 8 + i) ltac:(lia)). reflexivity.
Qed.
End seg89h.

(* ================= segments 8-9's tail: the second strcmp and the A -> B boundary B 0x821c4 (A 0x82068) ==========
   Both arms of the `n mod 4` test reach `jal strcmp` at 0x821c0 with a0 = text, a1 = want and ra = 0x821c4; only a0's
   ATOM differs (48 on the mod-4 arm, 18 on the other), so this step is generic in it. strcmp (text, want) compares a
   string with itself, so it returns 0: the `bnez a0` at 0x821c4 is the A -> B boundary, and its abort arm is UNTAKEN.
   crt_INV_82068 is then read off crt_keepA, crt_keep7 and the three strings. ---- *)
(* the stripped input holds no NUL: crt_base says the input holds none, and b64_strip only drops characters *)
Lemma a23_strip_nz : forall tb : list (bv 8), ~ In (Z_to_bv 8 0) tb ->
  ~ In 0 (B64Canon.b64_strip (HState.zs tb)).
Proof.
intros tb H Hin. apply (proj1 (filter_In _ _ _)) in Hin as (Hin & _).
unfold HState.zs in Hin. apply in_map_iff in Hin as (b & Hb & Hbin).
apply H. replace (Z_to_bv 8 0) with b; [exact Hbin|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Section cmp2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis IMG : fs_img_facts tfibsegs B.

Lemma a23_csF_in : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\
  YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) crt_csF.
Proof. unfold crt_csF. rewrite crt_frame3. apply Forall_cons; [cbn; lia | apply Forall_nil]. Qed.
Lemma a23_csF_atoms : crt_atom_chunks crt_csF.
Proof.
unfold crt_atom_chunks, crt_csF. apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil].
Qed.
Lemma a23_csF_off : Forall (fun c => 504 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 512)
  crt_csF.
Proof. unfold crt_csF. rewrite crt_frame3. apply Forall_cons; [cbn; lia | apply Forall_nil]. Qed.
Lemma a23_sv_in' : Forall (fun c => -104 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0)
  crt_sv_chunks.
Proof. unfold crt_sv_chunks. cbn [seq map]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma a23_cs1_in' : Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58)
  crt_cs1.
Proof. unfold crt_cs1. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

Lemma a23_strcmp_step : forall (ss : sstate) (r : Z) (na nb : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs)
  regsT memT mdT same (l1 l2 : list Z) (Q : world tfibsegs -> config -> Prop),
  crt_base B cx -> crt_E cx E ->
  sr_get (ss_regs ss) 1%bv = SLit r -> 0 <= r < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 r) ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
  sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
  sr_get (ss_regs ss) 10%bv = SOff na 0 -> sr_get (ss_regs ss) 11%bv = SOff nb 0 ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs))) ->
  cstr_ok tfibsegs W3 memT (bv_unsigned (ew E na)) l1 -> cstr_ok tfibsegs W3 memT (bv_unsigned (ew E nb)) l2 ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  crt_frame_ok cx S3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ->
  crt_keepA B cx same k ly3 S3 U3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ->
  crt_keep7 cx (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) W3 ->
  zbytes_at tfibsegs W3 memT same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_sp1 cx)) crt_cs1 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_F cx)) crt_csF ->
  (forall regs2 mem2 md2 (v : Z),
     crt_E cx (Ereg regs2 (crt_extra cx)) ->
     st_ok tfibsegs (Ereg regs2 (crt_extra cx)) (crt_ss_ret r crt_cs1 crt_csF)
       (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
     ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
     crt_frame_ok cx S3 W3 (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) ->
     crt_keepA B cx same k ly3 S3 U3 W3 (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) ->
     crt_keep7 cx (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) W3 ->
     zbytes_at tfibsegs W3 mem2 same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) ->
     aregs_preserved regsT regs2 -> YK11.getr regs2 10%bv = w64 v -> (v = 0 <-> str_eq l1 l2) ->
     SRr tfibsegs W3 (mkCfg (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) mdT) Q.
Proof.
intros ss r na nb cx E k ly3 S3 U3 W3 regsT memT mdT same l1 l2 Q HB HE Sr1 Hr HRet Sr2 Sr3 Sr4 Sr8 Sr9 Sr26 Sr10
  Sr11 HS HC1 HC2 HJ HARU HFO HK HK7 HZS HSV HCS1 HCSF K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
pose proof a23_STR as HSTR.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HFO as (Hfrs & Hnin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memT mdT k HJ HARU Hfrs)
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
assert (HF0' : 0 <= crt_F cx) by lia.
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in K20r, K21r, K24r, KP, KU, KH, K7, K8, K9, Ks1, Ks2, HX1, HX2, HI1, HI2, KF1, KF2, K12, K13, K14, K15,
  Kd1, Kd2, Kd3, Kd4, Kd5, Kp1, Kp2, Kwlo, Kwu, Ksh1, Ksh2, KRA.
pose proof HK7 as HK7'. destruct HK7' as (P27 & P23 & P22 & P19 & PZW).
cbn zeta in P27, P23, P22, P19, PZW.
cbn [ms_mem ms_regs mkst] in K8, K9, K12, K13, PZW, K20r, K21r, K24r, P27, P23, P22, P19, K7, KRA.
assert (HenL : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
  by exact (check_round_trip_loops.enc_len_Z (c_bs cx)).
assert (HenP : 0 <= (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
  by (pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)); lia).
refine (crt_rt_call2 SK B ss r na nb cx E k ly3 S3 U3 W3 regsT memT mdT l1 l2 _ RT IMG HB HE Sr1 Hr HRet
  Sr2 Sr3 Sr4 Sr10 Sr11 HS HC1 HC2 HJ HARU _).
intros regs2 mem2 md2 v HJ2 HARU2 HP2 Hv2 Hvr2 Hres2 Hfr2 Hgr2.
  assert (MBS : forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx) ->
    mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a)
    by (intros a Ha Hn; exact (mbyte_of_aview tfibsegs (w_H W3) (w_H W3) memT mem2 a (Hfr2 a Ha Hn))).
  assert (MB2 : forall a, 0 <= a < alloc_ceiling ->
    mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a)
    by (intros a Ha; apply MBS; lia).
  assert (HWS : forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
    writable_at tfibsegs (mrestrict (w_H W3) mem2) a).
  { intros a Ha. apply (apresent_writable tfibsegs). apply Hgr2.
    apply (YE7f.apresent_of_writable (w_H W3) memT a);
      [lia | apply a23_not_img; destruct Kp2 as [Hd|Hd]; unfold FS_IMG_END in *; lia
       | exact (proj1 (K12 a Ha))]. }
  assert (RQ : forall (q : bv 5) (z : Z), q = Z_to_bv 5 z -> acallee_saved z ->
    YK11.getr regs2 q = YK11.getr regsT q) by (intros q z -> Hz; exact (HP2 z Hz)).
  assert (CS : forall z, (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ (18 <= z <= 27)) -> acallee_saved z)
    by (intros z Hz; exact Hz).
  destruct (a23_D_keep B cx same k ly3 S3 U3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs))
    (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) HF0' HFceil
    ltac:(cbn [ms_mem mkst]; exact MB2) ltac:(cbn [ms_mem mkst]; exact HWS)
    ltac:(cbn [ms_regs mkst]; intros rr Hrr; cbn [In] in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]];
          [exact (RQ 20%bv 20 eq_refl ltac:(apply CS; lia)) | exact (RQ 21%bv 21 eq_refl ltac:(apply CS; lia))
          | exact (RQ 24%bv 24 eq_refl ltac:(apply CS; lia))])
    HK ltac:(cbn [ms_mem mkst]; exact PZW) ltac:(cbn [ms_mem mkst]; exact HZS) HFO)
    as (HK2 & HZW2 & HZS2 & HFO2).
  cbn [ms_mem ms_regs mkst] in HK2, HZW2, HZS2.
  pose proof HE as (E2v & E3v & E4v & E8v & E9v & E26v & EXv).
  assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
    by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
  assert (RA : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
  { intros q n Hq.
    pose proof (crt_reg_atom E (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ss q n HS Hq) as X.
    cbn [ms_regs mkst] in X. exact X. }
  assert (G2 : YK11.getr regs2 2%bv = Z_to_bv 64 (crt_sp1 cx))
    by exact (eq_trans (RQ 2%bv 2 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 2%bv 2%nat Sr2) (V 2%nat _ E2v ltac:(lia)))).
  assert (G3 : YK11.getr regs2 3%bv = YK11.getr (c_regs cx) 3%bv)
    by exact (eq_trans (RQ 3%bv 3 eq_refl ltac:(apply CS; lia)) (eq_trans (RA 3%bv 3%nat Sr3) E3v)).
  assert (G4 : YK11.getr regs2 4%bv = YK11.getr (c_regs cx) 4%bv)
    by exact (eq_trans (RQ 4%bv 4 eq_refl ltac:(apply CS; lia)) (eq_trans (RA 4%bv 4%nat Sr4) E4v)).
  assert (G8 : YK11.getr regs2 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
    by exact (eq_trans (RQ 8%bv 8 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 8%bv 8%nat Sr8) (V 8%nat _ E8v ltac:(unfold spZ; apply u64_range)))).
  assert (G9 : YK11.getr regs2 9%bv = Z_to_bv 64 (crt_sp1 cx))
    by exact (eq_trans (RQ 9%bv 9 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 9%bv 9%nat Sr9) (V 9%nat _ E9v ltac:(lia)))).
  assert (G26 : YK11.getr regs2 26%bv = Z_to_bv 64 (crt_SF cx))
    by exact (eq_trans (RQ 26%bv 26 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 26%bv 26%nat Sr26)
                   (V 26%nat _ E26v ltac:(pose proof (u64_range (ew E 26)); lia)))).
  assert (CH : forall base lo hi cs, 0 <= base + lo -> base + hi <= 2 ^ 64 ->
    Forall (fun c => lo <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
    (forall a, base + lo <= a < base + hi -> 0 <= a < alloc_ceiling \/
       ~ (crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx)) ->
    Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) base) cs ->
    Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem2) base) cs).
  { intros base lo hi cs Hb0 Hb1 Hin Hb Hc. rewrite Forall_forall in Hin, Hc |- *. intros c Hc'.
    apply (chunk_ok_mbyte E (mrestrict (w_H W3) memT)); [|exact (Hc c Hc')].
    intros i Hi. destruct (Hin c Hc') as (X1 & X2 & X3).
    destruct (Hb (base + YP09.c_off c + i) ltac:(lia)) as [Hl|Hl]; [apply MB2; lia|].
    apply MBS; [lia | exact Hl]. }
  destruct (a23_reseat SK B cx E k ly3 S3 U3 W3 regs2 mem2 md2 r crt_cs1 crt_csF
    HE H16 H0 Hceil0 H47 HJ2 HARU2 Hin3 G2 G3 G4 G8 G9 G26
    ltac:(apply (CH (spZ (c_regs cx)) (-104) 0 crt_sv_chunks ltac:(lia) ltac:(lia) a23_sv_in');
          [intros a Ha; right; lia | exact HSV])
    ltac:(apply (CH (crt_sp1 cx) 0x10 0x58 crt_cs1 ltac:(lia) ltac:(lia) a23_cs1_in');
          [intros a Ha; right; lia | exact HCS1])
    ltac:(apply (CH (crt_F cx) 504 512 crt_csF ltac:(lia) ltac:(lia) a23_csF_off);
          [intros a Ha; left; lia | exact HCSF])
    crt_cs1_in a23_csF_in crt_cs1_atoms a23_csF_atoms
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (HE' & HS').
  assert (HK72 : crt_keep7 cx (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) W3).
  { cbn zeta. cbn [ms_regs ms_mem mkst].
    split; [exact (eq_trans (RQ 27%bv 27 eq_refl ltac:(apply CS; lia)) P27)|].
    split; [exact (eq_trans (RQ 23%bv 23 eq_refl ltac:(apply CS; lia)) P23)|].
    split; [exact (eq_trans (RQ 22%bv 22 eq_refl ltac:(apply CS; lia)) P22)|].
    split; [exact (eq_trans (RQ 19%bv 19 eq_refl ltac:(apply CS; lia)) P19)|].
    exact HZW2. }
  exact (K regs2 mem2 md2 v HE' HS' HJ2 HARU2 HFO2 HK2 HK72 HZS2 HP2 Hv2 Hres2).
Qed.

Lemma a23_cmp2 : forall (ss : sstate) (na : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT same,
  crt_from SK B (crt_ss_ret 0x821c4 crt_cs1 crt_csF) (crt_INV_82068 B) ->
  crt_base B cx -> crt_E cx E ->
  sr_get (ss_regs ss) 1%bv = SLit 0x821c4 ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
  sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
  sr_get (ss_regs ss) 10%bv = SOff na 0 -> sr_get (ss_regs ss) 11%bv = SOff 49 0 ->
  bv_unsigned (ew E na) = c_text cx ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  crt_frame_ok cx S3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ->
  crt_keepA B cx same k ly3 S3 U3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ->
  crt_keep7 cx (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) W3 ->
  zbytes_at tfibsegs W3 memT same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) ->
  YK11.getr regsT 25%bv = w64 (c_t cx + Z.of_nat (length (c_tb cx))) ->
  YK11.getr regsT 18%bv = w64 (c_text cx) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_sp1 cx)) crt_cs1 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_F cx)) crt_csF ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) mdT) (crt_post SK B cx).
Proof.
intros ss na cx E k ly3 S3 U3 W3 regsT memT mdT same NEXT HB HE Sr1 Sr2 Sr3 Sr4 Sr8 Sr9 Sr26 Sr10 Sr11 Ena HS HJ HARU
  HFO HK HK7 HZS G25 G18 HSV HCS1 HCSF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
pose proof a23_STR as HSTR.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HFO as (Hfrs & Hnin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memT mdT k HJ HARU Hfrs)
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
assert (HF0' : 0 <= crt_F cx) by lia.
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in K20r, K21r, K24r, KP, KU, KH, K7, K8, K9, Ks1, Ks2, HX1, HX2, HI1, HI2, KF1, KF2, K12, K13, K14, K15,
  Kd1, Kd2, Kd3, Kd4, Kd5, Kp1, Kp2, Kwlo, Kwu, Ksh1, Ksh2, KRA.
pose proof HK7 as HK7'. destruct HK7' as (P27 & P23 & P22 & P19 & PZW).
cbn zeta in P27, P23, P22, P19, PZW.
cbn [ms_mem ms_regs mkst] in K8, K9, K12, K13, PZW, K20r, K21r, K24r, P27, P23, P22, P19, K7, KRA.
assert (HenL : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
  by exact (check_round_trip_loops.enc_len_Z (c_bs cx)).
assert (HenP : 0 <= (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
  by (pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)); lia).
assert (HBO : WriterSpec.bytes_ok (c_bs cx)).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDEC & _).
  exact (WriterSpecFacts.b64_dec_ok _ _ HDEC). }
assert (HNZ : ~ In 0 (WriterSpec.b64_enc (c_bs cx))) by exact (crt_enc_nz (c_bs cx) HBO).
assert (HinX : In (c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)
  (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; right; cbn [In]; tauto).
assert (HinW : In (c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; right; cbn [In]; tauto).
assert (HCT : cstr_ok tfibsegs W3 memT (c_text cx) (WriterSpec.b64_enc (c_bs cx))).
{ apply (crt_cstr_of_rblock B ly3 S3 U3 W3 memT mdT (c_text cx) (WriterSpec.b64_enc (c_bs cx))
    (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) HARU KH HinX (proj1 (proj2 K7)));
  [ rewrite HenL; unfold FSH_Fn_writer.enc_size; lia | exact K8 | exact HNZ ]. }
assert (HUW : forall q, In q U3 -> fst q + snd q <= c_want cx \/
  c_want cx + Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 <= fst q).
{ intros q Hq. rewrite HenL.
  pose proof (a23_U3_fresh B cx same k ly3 S3 U3 W3 _ memT mdT _ _ HB HARU HK (or_introl eq_refl)
    ltac:(unfold HEAD, FSH_Fn_writer.enc_size in *; lia) q Hq) as X.
  rewrite Z.add_assoc in X. exact X. }
assert (HCW : cstr_ok tfibsegs W3 memT (c_want cx) (WriterSpec.b64_enc (c_bs cx))).
{ apply (a23_cstr_of_block0 B ly3 S3 U3 W3 memT mdT (c_want cx) (WriterSpec.b64_enc (c_bs cx))
    (c_want cx) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) HARU KH HinW ltac:(lia)
    ltac:(rewrite HenL; lia) HUW PZW HNZ). }
assert (EW : bv_unsigned (ew E 49) = c_want cx) by (rewrite (crt_E_want cx E HE); apply wz; lia).
refine (crt_rt_call2 SK B ss 0x821c4 na 49%nat cx E k ly3 S3 U3 W3 regsT memT mdT
  (WriterSpec.b64_enc (c_bs cx)) (WriterSpec.b64_enc (c_bs cx)) _ RT IMG HB HE Sr1 ltac:(lia)
  ltac:(vm_compute; reflexivity) Sr2 Sr3 Sr4 Sr10 Sr11 HS _ _ HJ HARU _).
- rewrite Ena. exact HCT.
- rewrite EW. exact HCW.
- intros regs2 mem2 md2 v HJ2 HARU2 HP2 Hv2 Hvr2 Hres2 Hfr2 Hgr2.
  assert (Hv0 : v = 0) by (apply (proj2 Hres2); reflexivity). subst v.
  assert (MBS : forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx) ->
    mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a)
    by (intros a Ha Hn; exact (mbyte_of_aview tfibsegs (w_H W3) (w_H W3) memT mem2 a (Hfr2 a Ha Hn))).
  assert (MB2 : forall a, 0 <= a < alloc_ceiling ->
    mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a)
    by (intros a Ha; apply MBS; lia).
  assert (HWS : forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
    writable_at tfibsegs (mrestrict (w_H W3) mem2) a).
  { intros a Ha. apply (apresent_writable tfibsegs). apply Hgr2.
    apply (YE7f.apresent_of_writable (w_H W3) memT a);
      [lia | apply a23_not_img; destruct Kp2 as [Hd|Hd]; unfold FS_IMG_END in *; lia
       | exact (proj1 (K12 a Ha))]. }
  assert (RQ : forall (q : bv 5) (z : Z), q = Z_to_bv 5 z -> acallee_saved z ->
    YK11.getr regs2 q = YK11.getr regsT q) by (intros q z -> Hz; exact (HP2 z Hz)).
  assert (CS : forall z, (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ (18 <= z <= 27)) -> acallee_saved z)
    by (intros z Hz; exact Hz).
  destruct (a23_D_keep B cx same k ly3 S3 U3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs))
    (mkst regs2 (Z_to_bv 64 0x821c4) mem2 (seg_rom tfibsegs)) HF0' HFceil
    ltac:(cbn [ms_mem mkst]; exact MB2) ltac:(cbn [ms_mem mkst]; exact HWS)
    ltac:(cbn [ms_regs mkst]; intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[]]]];
          [exact (RQ 20%bv 20 eq_refl ltac:(apply CS; lia)) | exact (RQ 21%bv 21 eq_refl ltac:(apply CS; lia))
          | exact (RQ 24%bv 24 eq_refl ltac:(apply CS; lia))])
    HK ltac:(cbn [ms_mem mkst]; exact PZW) ltac:(cbn [ms_mem mkst]; exact HZS) HFO)
    as (HK2 & HZW2 & HZS2 & HFO2).
  cbn [ms_mem ms_regs mkst] in HK2, HZW2, HZS2.
  pose proof HE as (E2v & E3v & E4v & E8v & E9v & E26v & EXv).
  assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
    by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
  assert (RA : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
  { intros q n Hq.
    pose proof (crt_reg_atom E (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ss q n HS Hq) as X.
    cbn [ms_regs mkst] in X. exact X. }
  assert (G2 : YK11.getr regs2 2%bv = Z_to_bv 64 (crt_sp1 cx))
    by exact (eq_trans (RQ 2%bv 2 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 2%bv 2%nat Sr2) (V 2%nat _ E2v ltac:(lia)))).
  assert (G3 : YK11.getr regs2 3%bv = YK11.getr (c_regs cx) 3%bv)
    by exact (eq_trans (RQ 3%bv 3 eq_refl ltac:(apply CS; lia)) (eq_trans (RA 3%bv 3%nat Sr3) E3v)).
  assert (G4 : YK11.getr regs2 4%bv = YK11.getr (c_regs cx) 4%bv)
    by exact (eq_trans (RQ 4%bv 4 eq_refl ltac:(apply CS; lia)) (eq_trans (RA 4%bv 4%nat Sr4) E4v)).
  assert (G8 : YK11.getr regs2 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
    by exact (eq_trans (RQ 8%bv 8 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 8%bv 8%nat Sr8) (V 8%nat _ E8v ltac:(unfold spZ; apply u64_range)))).
  assert (G9 : YK11.getr regs2 9%bv = Z_to_bv 64 (crt_sp1 cx))
    by exact (eq_trans (RQ 9%bv 9 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 9%bv 9%nat Sr9) (V 9%nat _ E9v ltac:(lia)))).
  assert (G26 : YK11.getr regs2 26%bv = Z_to_bv 64 (crt_SF cx))
    by exact (eq_trans (RQ 26%bv 26 eq_refl ltac:(apply CS; lia))
                (eq_trans (RA 26%bv 26%nat Sr26)
                   (V 26%nat _ E26v ltac:(pose proof (u64_range (ew E 26)); lia)))).
  assert (CH : forall base lo hi cs, 0 <= base + lo -> base + hi <= 2 ^ 64 ->
    Forall (fun c => lo <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
    (forall a, base + lo <= a < base + hi -> 0 <= a < alloc_ceiling \/
       ~ (crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx)) ->
    Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) base) cs ->
    Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem2) base) cs).
  { intros base lo hi cs Hb0 Hb1 Hin Hb Hc. rewrite Forall_forall in Hin, Hc |- *. intros c Hc'.
    apply (chunk_ok_mbyte E (mrestrict (w_H W3) memT)); [|exact (Hc c Hc')].
    intros i Hi. destruct (Hin c Hc') as (X1 & X2 & X3).
    destruct (Hb (base + YP09.c_off c + i) ltac:(lia)) as [Hl|Hl]; [apply MB2; lia|].
    apply MBS; [lia | exact Hl]. }
  destruct (a23_reseat SK B cx E k ly3 S3 U3 W3 regs2 mem2 md2 0x821c4 crt_cs1 crt_csF
    HE H16 H0 Hceil0 H47 HJ2 HARU2 Hin3 G2 G3 G4 G8 G9 G26
    ltac:(apply (CH (spZ (c_regs cx)) (-104) 0 crt_sv_chunks ltac:(lia) ltac:(lia) a23_sv_in');
          [intros a Ha; right; lia | exact HSV])
    ltac:(apply (CH (crt_sp1 cx) 0x10 0x58 crt_cs1 ltac:(lia) ltac:(lia) a23_cs1_in');
          [intros a Ha; right; lia | exact HCS1])
    ltac:(apply (CH (crt_F cx) 504 512 crt_csF ltac:(lia) ltac:(lia) a23_csF_off);
          [intros a Ha; left; lia | exact HCSF])
    crt_cs1_in a23_csF_in crt_cs1_atoms a23_csF_atoms
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (HE' & HS').
  assert (HCT2 : cstr_ok tfibsegs W3 mem2 (c_text cx) (WriterSpec.b64_enc (c_bs cx))).
  { apply (crt_cstr_of_rblock B ly3 S3 U3 W3 mem2 md2 (c_text cx) (WriterSpec.b64_enc (c_bs cx))
      (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) HARU2 KH HinX (proj1 (proj2 K7)));
    [ rewrite HenL; unfold FSH_Fn_writer.enc_size; lia | | exact HNZ ].
    destruct HK2 as (_ & _ & _ & _ & _ & _ & _ & HZ2 & _). cbn zeta in HZ2. exact HZ2. }
  assert (EV : forall (q : bv 5) (n : nat) z, Z.of_nat n = bv_unsigned q ->
    YK11.getr regs2 q = Z_to_bv 64 z -> ew (Ereg regs2 (crt_extra cx)) n = Z_to_bv 64 z)
    by (intros q n z Hq Hw; rewrite (ew_Ereg_nat regs2 (crt_extra cx) n q Hq); exact Hw).
  pose proof HK2 as HK2'.
  destruct HK2' as (N20 & N21 & N24 & _ & _ & _ & N7 & N8 & N9 & _ & _ & _ & _ & _ & _ & _ & _ & N12 & N13 & N14
    & N15 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRA).
  cbn zeta in N20, N21, N24, N7, N8, N9, N12, N13, N14, N15, NRA.
  assert (HINV : crt_INV_82068 B cx (Ereg regs2 (crt_extra cx)) k ly3 S3 U3 W3
    (mkst regs2 (Z_to_bv 64 0x821c4) mem2 (seg_rom tfibsegs)) md2).
  { cbn zeta. cbn [ms_mem mkst].
    split; [exact (EV 10%bv 10%nat 0 ltac:(vm_compute; reflexivity) Hv2)|].
    split; [exact (EV 18%bv 18%nat _ ltac:(vm_compute; reflexivity)
             (eq_trans (RQ 18%bv 18 eq_refl ltac:(apply CS; lia)) G18))|].
    split; [exact (EV 20%bv 20%nat _ ltac:(vm_compute; reflexivity) N20)|].
    split; [exact (EV 21%bv 21%nat _ ltac:(vm_compute; reflexivity) N21)|].
    split; [exact (EV 27%bv 27%nat _ ltac:(vm_compute; reflexivity)
             (eq_trans (RQ 27%bv 27 eq_refl ltac:(apply CS; lia)) P27))|].
    split; [exact (EV 23%bv 23%nat _ ltac:(vm_compute; reflexivity)
             (eq_trans (RQ 23%bv 23 eq_refl ltac:(apply CS; lia)) P23))|].
    split; [exact (EV 22%bv 22%nat _ ltac:(vm_compute; reflexivity)
             (eq_trans (RQ 22%bv 22 eq_refl ltac:(apply CS; lia)) P22))|].
    split; [exact (EV 19%bv 19%nat _ ltac:(vm_compute; reflexivity)
             (eq_trans (RQ 19%bv 19 eq_refl ltac:(apply CS; lia)) P19))|].
    destruct N13 as (live & peak & cnt & Hglob & Hlive & Hcnt).
    exists same, live, peak, cnt.
    split; [exact (EV 24%bv 24%nat _ ltac:(vm_compute; reflexivity) N24)|].
    split; [exact (EV 25%bv 25%nat _ ltac:(vm_compute; reflexivity)
             (eq_trans (RQ 25%bv 25 eq_refl ltac:(apply CS; lia)) G25))|].
    split; [exact KP|]. split; [exact KU|]. split; [exact KH|].
    split; [exact N7|]. split; [exact N8|]. split; [exact HCT2|].
    split; [exact HZW2|]. split; [exact HZS2|]. split; [exact NRA|].
    split; [exact HenL|]. split; [exact Hglob|]. split; [exact Hlive|].
    split; [exact N14 | split; [exact Hcnt | exact N15]]. }
  exact (NEXT cx (Ereg regs2 (crt_extra cx)) k ly3 S3 U3 W3
    (mkst regs2 (Z_to_bv 64 0x821c4) mem2 (seg_rom tfibsegs)) md2 HB HE' HJ2 HARU2 HFO2 HINV HS').
Qed.
(* ---- the mod-4 arm after its first run: strcmp (text, same) at 0x821b0 returns 0 (B64Canon.canonical_enc: the
   stripped input IS the re-encoding when its length is a multiple of 4), so the abort arm 0x824e4 of `bnez a0` at
   0x821b4 is UNTAKEN; then `mv a0, s2` / `ld a1, 0x30(s1)` to the second strcmp, which a23_cmp2 takes. ---- *)
Lemma a23_eq1 : forall (ss : sstate) (na nb : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT same,
  crt_from SK B (crt_ss_ret 0x821c4 crt_cs1 crt_csF) (crt_INV_82068 B) ->
  crt_base B cx -> crt_E cx E ->
  Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) mod 4 = 0 ->
  sr_get (ss_regs ss) 1%bv = SLit 0x821b4 ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
  sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
  sr_get (ss_regs ss) 10%bv = SOff na 0 -> sr_get (ss_regs ss) 11%bv = SOff nb 0 ->
  bv_unsigned (ew E na) = c_text cx -> bv_unsigned (ew E nb) = same ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  crt_frame_ok cx S3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ->
  crt_keepA B cx same k ly3 S3 U3 W3 (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ->
  crt_keep7 cx (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) W3 ->
  zbytes_at tfibsegs W3 memT same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) ->
  YK11.getr regsT 25%bv = w64 (c_t cx + Z.of_nat (length (c_tb cx))) ->
  YK11.getr regsT 18%bv = w64 (c_text cx) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_sp1 cx)) crt_cs1 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_F cx)) crt_csF ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) mdT) (crt_post SK B cx).
Proof.
intros ss na nb cx E k ly3 S3 U3 W3 regsT memT mdT same NEXT HB HE Hm0 Sr1 Sr2 Sr3 Sr4 Sr8 Sr9 Sr26 Sr10 Sr11
  Ena Enb HS HJ HARU HFO HK HK7 HZS G25 G18 HSV HCS1 HCSF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in K7, K8, KP, KH, Ks1, Ks2, Kd3. cbn [ms_mem mkst] in K7, K8.
pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & HTNZ & HTL & _ & _ & HDEC & _).
assert (HenL : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
  by exact (check_round_trip_loops.enc_len_Z (c_bs cx)).
assert (HNZ : ~ In 0 (WriterSpec.b64_enc (c_bs cx)))
  by exact (crt_enc_nz (c_bs cx) (WriterSpecFacts.b64_dec_ok _ _ HDEC)).
pose proof (a23_strip_len0 (HState.zs (c_tb cx))) as SL. rewrite a23_zs_len0 in SL.
assert (HinX : In (c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)
  (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; right; cbn [In]; tauto).
assert (HinS : In (same, Z.of_nat (length (c_tb cx)) + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; right; cbn [In]; tauto).
assert (HCT : cstr_ok tfibsegs W3 memT (c_text cx) (WriterSpec.b64_enc (c_bs cx))).
{ apply (crt_cstr_of_rblock B ly3 S3 U3 W3 memT mdT (c_text cx) (WriterSpec.b64_enc (c_bs cx))
    (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) HARU KH HinX (proj1 (proj2 K7)));
  [ rewrite HenL; unfold FSH_Fn_writer.enc_size; lia | exact K8 | exact HNZ ]. }
assert (HCS : cstr_ok tfibsegs W3 memT same (B64Canon.b64_strip (HState.zs (c_tb cx)))).
{ apply (a23_cstr_of_block0 B ly3 S3 U3 W3 memT mdT same (B64Canon.b64_strip (HState.zs (c_tb cx)))
    same (Z.of_nat (length (c_tb cx)) + 1) HARU KH HinS ltac:(lia) ltac:(lia)); [| exact HZS |].
  - intros q Hq.
    pose proof (a23_U3_fresh B cx same k ly3 S3 U3 W3 _ memT mdT same (Z.of_nat (length (c_tb cx)) + 1)
      HB HARU HK (or_intror (or_introl eq_refl)) ltac:(unfold HEAD, FSH_Fn_writer.enc_size in *; lia) q Hq) as X.
    lia.
  - exact (a23_strip_nz (c_tb cx) HTNZ). }
apply (a23_strcmp_step ss 0x821b4 na nb cx E k ly3 S3 U3 W3 regsT memT mdT same
  (WriterSpec.b64_enc (c_bs cx)) (B64Canon.b64_strip (HState.zs (c_tb cx))) _ HB HE Sr1 ltac:(lia)
  ltac:(vm_compute; reflexivity) Sr2 Sr3 Sr4 Sr8 Sr9 Sr26 Sr10 Sr11 HS ltac:(rewrite Ena; exact HCT)
  ltac:(rewrite Enb; exact HCS) HJ HARU HFO HK HK7 HZS HSV HCS1 HCSF).
intros regs2 mem2 md2 v HE' HS' HJ2 HARU2 HFO2 HK2 HK72 HZS2 HP2 Hv2 Hres2.
(* the first strcmp returned 0 *)
assert (Hv0 : v = 0).
{ apply (proj2 Hres2). unfold str_eq. symmetry.
  exact (B64Canon.canonical_enc (HState.zs (c_tb cx)) (c_bs cx) HDEC Hm0). }
subst v.
set (E3 := Ereg regs2 (crt_extra cx)) in *.
(* what the run from 0x821b4 reads off the boundary state *)
assert (R3 : forall (q : bv 5) n, sr_get (ss_regs (crt_ss_ret 0x821b4 crt_cs1 crt_csF)) q = SOff n 0 ->
  YK11.getr regs2 q = ew E3 n)
  by (intros q n Hq; exact (crt_reg_atom E3 (w_H W3) (mkst regs2 (Z_to_bv 64 0x821b4) mem2 (seg_rom tfibsegs))
        _ q n HS' Hq)).
assert (HCSF3 : Forall (YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W3) mem2) (crt_F cx)) crt_csF).
{ pose proof (fsw_region_nth E3 _ _ 2 (crt_frame_region crt_csF) HS' eq_refl) as (_ & _ & _ & Hc).
  cbn [crt_frame_region YP09.r_base YP09.r_chunks base_val ms_mem restrict mkst] in Hc.
  assert (EFv : bv_unsigned (ew E3 47) = crt_F cx)
    by (rewrite (crt_E_F cx E3 HE'); apply wz; destruct (crt_F_facts SK B cx ly3 S3 U3 W3 mem2 md2 k HJ2 HARU2
          (proj1 HFO2)) as (_ & HF1 & HF2 & _); lia).
  rewrite EFv in Hc. exact Hc. }
pose proof (st_ok_submem tfibsegs E3 _ _ _ HS' (a23_sub2 0x821b4 crt_cs1 crt_csF)
  ltac:(vm_compute; reflexivity)) as HS4.
change (st_ok tfibsegs E3 (a23_ss2 0x821b4 crt_cs1)
  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 0x821b4) mem2 (seg_rom tfibsegs)))) in HS4.
assert (HS5 : st_ok tfibsegs E3 a23_base2858
  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 0x821b4) mem2 (seg_rom tfibsegs)))).
{ apply (st_ok_set_reg tfibsegs E3 _ _ 10%bv (SLit 0) HS4).
  - intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
  - cbn [ms_regs restrict mkst sv_denot]. exact Hv2. }
clear HS4.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 mem2 md2 k HJ2 HARU2 (proj1 HFO2))
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
fsw_aj_run_toU crt_tbl_ok HS5 HJ2 HARU2 PC_strcmp.
{ exact (a23_awr2 B cx E3 ly3 S3 crt_cs1 HB HE'). }
(* the run writes only stack bytes above the ceiling *)
assert (HSB : same_below mem2 (ms_mem ms) alloc_ceiling)
  by exact (a23_sb B cx E3 crt_cs1 _ _ HB HE' HF).
assert (MB : forall a, 0 <= a < alloc_ceiling ->
  mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W3) mem2) a)
  by (intros a Ha; apply a23_mb_of_raw; exact (HSB a Ha)).
(* the machine's registers after the run: the engine keeps 18 and 19 .. 27 as their own atoms *)
assert (EQR : forall (q : bv 5) (n : nat), Z.of_nat n = bv_unsigned q -> ew E3 n = YK11.getr regs2 q)
  by (intros q n Hq; unfold E3; exact (ew_Ereg_nat regs2 (crt_extra cx) n q Hq)).
assert (MR : forall (q : bv 5) (n : nat), Z.of_nat n = bv_unsigned q ->
  (forall SS, st_ok tfibsegs E3 SS (restrict (w_H W3) ms) -> sr_get (ss_regs SS) q = SOff n 0 ->
     YK11.getr (ms_regs ms) q = YK11.getr regs2 q)).
{ intros q n Hq SS HSS Hr. rewrite (crt_reg_atom E3 (w_H W3) ms SS q n HSS Hr). exact (EQR q n Hq). }
assert (P19 : YK11.getr (ms_regs ms) 19%bv = YK11.getr regs2 19%bv)
  by (eapply (MR 19%bv 19%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P20 : YK11.getr (ms_regs ms) 20%bv = YK11.getr regs2 20%bv)
  by (eapply (MR 20%bv 20%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P21 : YK11.getr (ms_regs ms) 21%bv = YK11.getr regs2 21%bv)
  by (eapply (MR 21%bv 21%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P22 : YK11.getr (ms_regs ms) 22%bv = YK11.getr regs2 22%bv)
  by (eapply (MR 22%bv 22%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P23 : YK11.getr (ms_regs ms) 23%bv = YK11.getr regs2 23%bv)
  by (eapply (MR 23%bv 23%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P24 : YK11.getr (ms_regs ms) 24%bv = YK11.getr regs2 24%bv)
  by (eapply (MR 24%bv 24%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P25 : YK11.getr (ms_regs ms) 25%bv = YK11.getr regs2 25%bv)
  by (eapply (MR 25%bv 25%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P26 : YK11.getr (ms_regs ms) 26%bv = YK11.getr regs2 26%bv)
  by (eapply (MR 26%bv 26%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P27 : YK11.getr (ms_regs ms) 27%bv = YK11.getr regs2 27%bv)
  by (eapply (MR 27%bv 27%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (P18 : YK11.getr (ms_regs ms) 18%bv = YK11.getr regs2 18%bv)
  by (eapply (MR 18%bv 18%nat eq_refl); [exact HS5 | vm_compute; reflexivity]).
assert (CS : forall z, (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ (18 <= z <= 27)) -> acallee_saved z)
  by (intros z Hz; exact Hz).
assert (Q18 : YK11.getr regs2 18%bv = YK11.getr regsT 18%bv) by exact (HP2 18 ltac:(apply CS; lia)).
assert (Q25 : YK11.getr regs2 25%bv = YK11.getr regsT 25%bv) by exact (HP2 25 ltac:(apply CS; lia)).
(* the bundle at the call site of the second strcmp *)
assert (HWS : forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
  writable_at tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a).
{ intros a Ha. destruct HK2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K12' & _).
  cbn zeta in K12'. eapply writable_at_grows; [exact HG | exact (proj1 (K12' a Ha))]. }
destruct (a23_D_keep B cx same k ly3 S3 U3 W3 (mkst regs2 (Z_to_bv 64 0x821b4) mem2 (seg_rom tfibsegs)) ms
  ltac:(lia) HFceil ltac:(cbn [ms_mem mkst]; exact MB) HWS
  ltac:(cbn [ms_regs mkst]; intros rr Hrr; cbn [In] in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]];
        [exact P20 | exact P21 | exact P24])
  HK2 ltac:(destruct HK72 as (_ & _ & _ & _ & HZ); exact HZ) ltac:(cbn [ms_mem mkst]; exact HZS2) HFO2)
  as (HK3 & HZW3 & HZS3 & HFO3).
assert (HK73 : crt_keep7 cx ms W3).
{ destruct HK72 as (Z27 & Z23 & Z22 & Z19 & _). cbn zeta in Z27, Z23, Z22, Z19. cbn [ms_regs mkst] in Z27, Z23, Z22, Z19.
  split; [rewrite P27; exact Z27|]. split; [rewrite P23; exact Z23|].
  split; [rewrite P22; exact Z22|]. split; [rewrite P19; exact Z19 | exact HZW3]. }
assert (HCSF4 : Forall (YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crt_csF).
{ apply (a23_chunks_mb E3 (mrestrict (w_H W3) mem2) (mrestrict (w_H W3) (ms_mem ms)) _ _ 504 512 a23_csF_off);
    [intros a Ha; apply MB; lia | exact HCSF3]. }
assert (HSV4 : Forall (YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W3) (ms_mem ms)) (spZ (c_regs cx))) crt_sv_chunks).
{ pose proof (fsw_region_nth E3 _ _ 0 crt_s0_region HS5 eq_refl) as (_ & _ & _ & Hc).
  cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hc.
  pose proof HE' as (_ & _ & _ & E8v & _). rewrite E8v in Hc. exact Hc. }
assert (HCS14 : Forall (YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) crt_cs1).
{ pose proof (fsw_region_nth E3 _ _ 1 (crt_slot_region crt_cs1) HS5 eq_refl) as (_ & _ & _ & Hc).
  cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hc.
  pose proof HE' as (_ & _ & _ & _ & E9v & _). rewrite E9v in Hc. exact Hc. }
assert (Ena3 : bv_unsigned (ew E3 18) = c_text cx).
{ rewrite (EQR 18%bv 18%nat eq_refl), Q18, G18. unfold w64. apply wz.
  destruct HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX1' & HX2' & _). cbn zeta in HX1', HX2'.
  unfold HEAD, FSH_Fn_writer.enc_size in *. pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)).
  vm_compute YM05.CEIL_MAX in HACV. lia. }
assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 PC_strcmp) (ms_mem ms) (seg_rom tfibsegs))
  by (apply (crt_mkst (w_H W3) _ _ ms HS5); reflexivity).
rewrite Ems in HS5, HK3, HK73, HFO3 |- *.
refine (a23_cmp2 _ 18%nat cx E3 k ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) _ same NEXT HB HE'
  _ _ _ _ _ _ _ _ _ Ena3 HS5 HJ2 HARU2 HFO3 HK3 HK73 HZS3
  ltac:(rewrite P25, Q25; exact G25) ltac:(rewrite P18, Q18; exact G18) HSV4 HCS14 HCSF4);
  vm_compute; reflexivity.
Qed.

End cmp2.

(* ================= segments 8-9, B 0x82180 -> 0x821c4: the from-lemma of this lane's second piece =================
   The UBSan test `bltu a2, a1` at 0x82180 (B only, trap arm 0x82620 untaken), the NUL store at 0x8219c with its ASan
   check (slow path 0x82630 -> 0x82198; __asan_report_store1 at 0x82638 UNTAKEN), `ld s2, 0x18(s1)` (text), and the
   `n mod 4` test at 0x821a4. On the mod-4 arm the walk first compares text with `same`: `same` holds b64_strip (zs tb),
   and B64Canon.canonical_enc says that IS b64_enc bs when its length is a multiple of 4, so strcmp returns 0 and the
   abort arm 0x824e4 of `bnez a0` at 0x821b4 is UNTAKEN. Both arms then reach the second strcmp, which a23_cmp2 takes
   to the A -> B boundary (A: 0x82028 -> 0x82068). ---- *)
Section seg89. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis IMG : fs_img_facts tfibsegs B.


(* the run state of segments 8-9: the boundary at B 0x82180 without the frame's two regions, plus a one-byte write
   region at the store's address (a fresh atom 51 = crt_xatom 0, which the alias facts name as s8 + a1), the atoms the
   branches read (a2 = ~same for the UBSan test), and the `n mod 4` case condition. *)
Lemma a23_st28 : forall (c : branch_cond) cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 same v51,
  crt_base B cx -> crt_E cx E ->
  crt_INV_82028 cx E k ly3 S3 U3 W3 ms3 md3 ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms3 ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  YK11.getr (ms_regs ms3) 24%bv = w64 same ->
  bv_unsigned v51 = same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) ->
  branch_taken c (sv_denot (ewset E 51 v51) (SAlu ALU_AND (SOff 11 0) (SLit 3)))
    (sv_denot (ewset E 51 v51) (SLit 0)) = true ->
  st_ok tfibsegs E (crt_ss_ret 0x82180 crt_cs1 crt_csF) (restrict (w_H W3) ms3) ->
  st_ok tfibsegs (ewset E 51 v51) (a23_tok28 c) (restrict (w_H W3) ms3) /\
  sh_ok tfibsegs fs_Bx a23_SH28 (ewset E 51 v51) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros c cx E k ly3 S3 U3 W3 ms3 md3 same v51 HB HE HI HK HARU G24 EV51 HC HS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in K12, Ks1, Ks2, KP.
destruct HI as (same0 & I25 & I13 & I11 & I24 & I18 & I14 & I16 & I12 & I15 & IZS & IZT & Is1 & Is2).
cbn zeta in I25, I13, I11, I24, I18, I14, I16, I12, I15, IZS, IZT, Is1, Is2.
assert (Esm : same0 = same).
{ rewrite I24 in G24. apply (f_equal (@bv_unsigned 64)) in G24. unfold w64 in G24.
  rewrite (wz same0 ltac:(lia)), (wz same ltac:(lia)) in G24. exact G24. }
subst same0.
pose proof (a23_strip_len0 (HState.zs (c_tb cx))) as SL. rewrite a23_zs_len0 in SL.
pose proof (Nat2Z.is_nonneg (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) as SL0.
pose proof (Nat2Z.is_nonneg (length (c_tb cx))) as SL1.
pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & HTNZ & HTL & _).
vm_compute YM05.CEIL_MAX in HACV.
assert (HenP : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))
  by (unfold FSH_Fn_writer.enc_size;
      pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)); lia).
unfold HEAD in HX1.
(* the env's atoms the run reads *)
set (E1 := ewset E 51 v51) in *.
assert (HAG : env_agree 51 E E1) by apply env_agree_ewset.
assert (HE1 : crt_E cx E1) by exact (a23_E_agree cx E E1 HAG HE).
assert (A : forall (q : bv 5) n, sr_get (ss_regs (crt_ss_ret 0x82180 crt_cs1 crt_csF)) q = SOff n 0 ->
  YK11.getr (ms_regs ms3) q = ew E n) by (intros q n Hq; exact (crt_reg_atom E (w_H W3) ms3 _ q n HS Hq)).
assert (EA24 : bv_unsigned (ew E1 24) = same).
{ rewrite (proj1 HAG 24%nat ltac:(lia)), <- (A 24%bv 24%nat ltac:(vm_compute; reflexivity)), G24.
  unfold w64. apply wz. lia. }
assert (EA11 : bv_unsigned (ew E1 11)
  = Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))).
{ rewrite (proj1 HAG 11%nat ltac:(lia)), <- (A 11%bv 11%nat ltac:(vm_compute; reflexivity)), I11.
  unfold w64. apply wz. lia. }
assert (EA12 : bv_unsigned (ew E1 12) = 2 ^ 64 - 1 - same).
{ rewrite (proj1 HAG 12%nat ltac:(lia)), <- (A 12%bv 12%nat ltac:(vm_compute; reflexivity)), I12.
  unfold w64. apply wz. lia. }
assert (EA48 : bv_unsigned (ew E1 48) = c_text cx)
  by (rewrite (proj1 HAG 48%nat ltac:(lia)), (crt_E_text cx E HE); apply wz; lia).
assert (EA32 : bv_unsigned (ew E1 32) = SHADOW_OFF)
  by (rewrite (proj1 HAG 32%nat ltac:(lia)), (crt_E_shadow cx E HE); apply wz; unfold SHADOW_OFF; lia).
assert (EA51 : bv_unsigned (ew E1 51) = same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))))
  by (unfold E1; rewrite ew_ewset_same; exact EV51).
(* the state *)
pose proof (st_ok_agree tfibsegs 51 E E1 _ _ HS HAG ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_submem tfibsegs E1 _ _ _ HS0 (a23_sub2 0x82180 crt_cs1 crt_csF)
  ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E1 (a23_ss2 0x82180 crt_cs1) (restrict (w_H W3) ms3)) in HS2.
assert (HS3 : st_ok tfibsegs E1
  (mkSS (ss_pc (a23_ss2 0x82180 crt_cs1)) (sr_set (ss_regs (a23_ss2 0x82180 crt_cs1)) 18%bv (SOff 32 0))
     (ss_mem (a23_ss2 0x82180 crt_cs1)) (ss_resv (a23_ss2 0x82180 crt_cs1))
     (ss_facts (a23_ss2 0x82180 crt_cs1))) (restrict (w_H W3) ms3)).
{ apply (st_ok_set_reg tfibsegs E1 _ _ 18%bv (SOff 32 0) HS2).
  - intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
  - cbn [ms_regs restrict]. rewrite fsw_SOff0, I18. apply bv_eq. rewrite EA32. unfold w64.
    rewrite (wz SHADOW_OFF ltac:(unfold SHADOW_OFF; lia)). reflexivity. }
assert (HRW : region_ok tfibsegs E1 (mrestrict (w_H W3) (ms_mem ms3)) (a23_wr 51)).
{ unfold region_ok, a23_wr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EA51.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho.
  replace (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) + o)
    with (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) by lia.
  exact (proj1 (K12 (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) ltac:(lia))). }
assert (HS4 : st_ok tfibsegs E1 a23_base28 (restrict (w_H W3) ms3)).
{ apply (st_ok_add_region' tfibsegs E1 _ _ (a23_wr 51) HS3 ltac:(vm_compute; reflexivity)).
  - cbn [ms_mem restrict]. exact HRW.
  - apply all_disjoint_of_extents.
    unfold a23_ss2. cbn [ss_mem map].
    unfold extent_of_region, base_val, a23_wr, crt_s0_region, fs_ret_s0_region, crt_slot_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite EA51.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HE1))))) as E9x.
    pose proof (proj1 (proj2 (proj2 (proj2 HE1)))) as E8x.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I; first [left; lia | right; lia]. }
split.
- unfold a23_tok28.
  apply (st_ok_add_cond tfibsegs E1 _ _ c (SAlu ALU_AND (SOff 11 0) (SLit 3)) (SLit 0));
    [|exact HC].
  apply (st_ok_add_alias tfibsegs E1); [apply (st_ok_add_alias tfibsegs E1)|].
  + apply (st_ok_add_fact tfibsegs E1 _ _ 12%nat a23_nsm);
      [apply (st_ok_add_fact tfibsegs E1 _ _ 32%nat a23_shb);
         [apply (st_ok_add_fact tfibsegs E1 _ _ 51%nat a23_af);
            [apply (st_ok_add_fact tfibsegs E1 _ _ 24%nat a23_af);
               [apply (st_ok_add_fact tfibsegs E1 _ _ 11%nat (mkAF 0 3145728 0));
                  [apply (st_ok_add_fact tfibsegs E1 _ _ 48%nat a23_af); [exact HS4|] | ] | ] | ] | ] | ];
      unfold afact_ok, a23_af, a23_shb, a23_nsm; cbn [af_lo af_hi af_al2].
    * rewrite EA48. split; [lia | split; [apply Z.mod_1_r | lia]].
    * rewrite EA11. split; [lia | split; [apply Z.mod_1_r | lia]].
    * rewrite EA24. split; [lia | split; [apply Z.mod_1_r | lia]].
    * rewrite EA51. split; [lia | split; [apply Z.mod_1_r | lia]].
    * rewrite EA32. split; [lia | split; [apply Z.mod_1_r | lia]].
    * rewrite EA12. split; [lia | split; [apply Z.mod_1_r | lia]].
  + assert (R24 : ew E1 24 = Z_to_bv 64 same)
      by (apply bv_eq; rewrite EA24; symmetry; apply wz; lia).
    assert (R11 : ew E1 11 = Z_to_bv 64 (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))))
      by (apply bv_eq; rewrite EA11; symmetry; apply wz; lia).
    cbn [sv_denot]. rewrite !Z.add_0_r, EA51, R24, R11, alu64_add_lit.
    rewrite (wz same ltac:(lia)), (wz (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) ltac:(lia)). apply f_equal. lia.
  + assert (R24 : ew E1 24 = Z_to_bv 64 same)
      by (apply bv_eq; rewrite EA24; symmetry; apply wz; lia).
    assert (R11 : ew E1 11 = Z_to_bv 64 (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))))
      by (apply bv_eq; rewrite EA11; symmetry; apply wz; lia).
    cbn [sv_denot]. rewrite !Z.add_0_r, EA51, R24, R11, alu64_add_lit.
    rewrite (wz same ltac:(lia)), (wz (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) ltac:(lia)). apply f_equal. lia.
- unfold sh_ok, a23_SH28. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range tfibsegs (w_H W3) (ms_mem ms3) E1 fs_Bx 51
    (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) 1
    (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) 0 1).
  + apply (a23_block_addr_noU B ly3 S3 U3 W3 (ms_mem ms3) md3 same (Z.of_nat (length (c_tb cx)) + 1)
      (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) 1
      HARU KH ltac:(apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; right; cbn [In]; tauto)
      ltac:(lia) ltac:(lia)
      ltac:(unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (c_tb cx)) + 1) 0); lia)).
    intros q Hq.
    pose proof (a23_U3_fresh B cx same k ly3 S3 U3 W3 ms3 (ms_mem ms3) md3 same (Z.of_nat (length (c_tb cx)) + 1)
      HB HARU HK (or_intror (or_introl eq_refl)) ltac:(unfold HEAD, FSH_Fn_writer.enc_size in *; lia) q Hq) as X.
    lia.
  + unfold fs_Bx. apply (U_atom E1 32 SHADOW_OFF ltac:(apply bv_eq; rewrite EA32; symmetry; apply wz;
      unfold SHADOW_OFF; lia)). unfold SHADOW_OFF. lia.
  + apply (U_atom E1 51 _ ltac:(apply bv_eq; rewrite EA51; symmetry; apply wz; lia)). lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. apply Ksh2. lia.
Qed.

(* the `n mod 4` test's condition, read on atom 11 (B's index register a1; A: atom 12, a2) *)
Lemma a23_mod4_bt : forall E (L : Z), bv_unsigned (ew E 11) = L -> 0 <= L ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff 11 0) (SLit 3))) (sv_denot E (SLit 0)) = (L mod 4 =? 0).
Proof.
intros E L HL H0. cbn [branch_taken sv_denot]. rewrite bv_eqb_unsigned, YO0c.alu64_and, Z.add_0_r,
  Z_to_bv_bv_unsigned, HL, (wz 3 ltac:(lia)), (wz 0 ltac:(lia)).
change 3 with (Z.ones 2). rewrite (Z.land_ones L 2 ltac:(lia)). reflexivity.
Qed.

(* the data the walk carries over segs 8-9's first run: everything below alloc_ceiling is kept but the store's byte
   same + |strip|, which now holds the NUL *)
Lemma a23_run1_post : forall cx same k ly3 S3 U3 (W3 : world tfibsegs) (ms3 ms : machine_state),
  4096 <= crt_F cx -> crt_F cx + 512 <= alloc_ceiling ->
  (forall a, 0 <= a < alloc_ceiling ->
     a <> same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) ->
     mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) a) ->
  val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms))
    (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) 1 0 ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  (forall r : bv 5, In r [19; 20; 21; 22; 23; 24; 26; 27]%bv -> YK11.getr (ms_regs ms) r = YK11.getr (ms_regs ms3) r) ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms3 -> crt_keep7 cx ms3 W3 ->
  zbytes_at tfibsegs W3 (ms_mem ms3) same (B64Canon.b64_strip (HState.zs (c_tb cx))) ->
  crt_frame_ok cx S3 W3 ms3 ->
  (crt_F cx + 512 <= same \/ same + Z.of_nat (length (c_tb cx)) + 1 <= crt_F cx) ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms /\ crt_keep7 cx ms W3 /\
  zbytes_at tfibsegs W3 (ms_mem ms) same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) /\
  crt_frame_ok cx S3 W3 ms.
Proof.
intros cx same k ly3 S3 U3 W3 ms3 ms HF1 HF2 HM HNUL HG HR HK HK7 HZS HFO HFS.
pose proof HK as HK'.
destruct HK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ks1 & Ks2 & _ & _ & _ & _ & _ & _ & K12 & _ & _ & _
  & Kd1 & _ & _ & _ & _ & _ & _ & Kwlo & Kwu & _).
cbn zeta in Ks1, Ks2, K12, Kd1, Kwlo, Kwu.
pose proof (a23_strip_len0 (HState.zs (c_tb cx))) as SL. rewrite a23_zs_len0 in SL.
pose proof (Nat2Z.is_nonneg (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) as SL0.
pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)) as HDP.
split.
{ apply (a23_keepA_keep B cx same k ly3 S3 U3 W3 ms3 ms HF1 HF2).
  - intros a Ha Hr. destruct (a23_rd_facts B cx same k ly3 S3 U3 W3 ms3 HK a Hr) as (F1 & _ & F3).
    exact (HM a F1 F3).
  - intros a Ha. eapply writable_at_grows; [exact HG | exact (proj1 (K12 a Ha))].
  - intros r Hr. apply HR. cbn [In] in Hr |- *. tauto.
  - exact HK. }
split.
{ destruct HK7 as (P27 & P23 & P22 & P19 & PZW). cbn zeta in P27, P23, P22, P19, PZW.
  split; [rewrite (HR 27%bv ltac:(cbn [In]; tauto)); exact P27|].
  split; [rewrite (HR 23%bv ltac:(cbn [In]; tauto)); exact P23|].
  split; [rewrite (HR 22%bv ltac:(cbn [In]; tauto)); exact P22|].
  split; [rewrite (HR 19%bv ltac:(cbn [In]; tauto)); exact P19|].
  apply (garr8_frame tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms))); [exact PZW|].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  rewrite Nat2Z.inj_add, (check_round_trip_loops.enc_len_Z (c_bs cx)) in Ha. cbn [Z.of_nat] in Ha.
  apply HM; lia. }
split.
{ apply (garr8_app1 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) same
    (B64Canon.b64_strip (HState.zs (c_tb cx))) 0 HZS HNUL ltac:(lia)).
  intros a Ha. apply HM; lia. }
destruct HFO as (Hfrs & Hnin & Hflag). split; [exact Hfrs|]. split; [exact Hnin|].
rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3.
unfold aview. rewrite (HM (crt_F cx + 512 - 8 + i) ltac:(lia) ltac:(lia)). reflexivity.
Qed.
(* the data after segs 8-9's first run, at the call site of a strcmp, from the run's frame and its post state SS *)
Lemma a23_post28 : forall (c : branch_cond) cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 (ms : machine_state)
  same v51 E2 (SS : sstate),
  crt_base B cx -> crt_E cx E -> bv_unsigned v51 = same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  crt_INV_82028 cx E k ly3 S3 U3 W3 ms3 md3 ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms3 -> crt_keep7 cx ms3 W3 ->
  YK11.getr (ms_regs ms3) 24%bv = w64 same ->
  st_ok tfibsegs E (crt_ss_ret 0x82180 crt_cs1 crt_csF) (restrict (w_H W3) ms3) ->
  (forall n, (n <= 51)%nat -> ew E2 n = ew (ewset E 51 v51) n) ->
  frame_of (ewset E 51 v51) (ss_mem (a23_tok28 c)) (ms_mem ms3) (ms_mem ms) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  st_ok tfibsegs E2 SS (restrict (w_H W3) ms) ->
  nth_error (ss_mem SS) 0 = Some (YP09.mkRegion (Some 51%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) ->
  nth_error (ss_mem SS) 1 = Some crt_s0_region -> nth_error (ss_mem SS) 2 = Some (crt_slot_region crt_cs1) ->
  (forall q : bv 5, In q [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
     sr_get (ss_regs SS) q = SOff (if bv_eqb q 18%bv then 48%nat else Z.to_nat (bv_unsigned q)) 0) ->
  crt_keepA B cx same k ly3 S3 U3 W3 ms /\ crt_keep7 cx ms W3 /\
  zbytes_at tfibsegs W3 (ms_mem ms) same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) /\
  crt_frame_ok cx S3 W3 ms /\
  YK11.getr (ms_regs ms) 25%bv = w64 (c_t cx + Z.of_nat (length (c_tb cx))) /\
  YK11.getr (ms_regs ms) 18%bv = w64 (c_text cx) /\
  Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) (ms_mem ms)) (spZ (c_regs cx))) crt_sv_chunks /\
  Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) crt_cs1 /\
  Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crt_csF.
Proof.
intros c cx E k ly3 S3 U3 W3 ms3 md3 ms same v51 E2 SS HB HE EV51 HJ HARU HFO HI HK HK7 G24 HS HAG2 HF HG HS2
  N0 N1 N2 RG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (a23_spf B cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HFO as (Hfrs & Hnin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfrs)
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in Ks1, Ks2, KP, HX1, HX2.
destruct HI as (same0 & I25 & I13 & I11 & I24 & I18 & I14 & I16 & I12 & I15 & IZS & IZT & Is1 & Is2).
cbn zeta in I25, I13, I11, I24, I18, I14, I16, I12, I15, IZS, IZT, Is1, Is2.
assert (Esm : same0 = same).
{ rewrite I24 in G24. apply (f_equal (@bv_unsigned 64)) in G24. unfold w64 in G24.
  rewrite (wz same0 ltac:(lia)), (wz same ltac:(lia)) in G24. exact G24. }
subst same0.
pose proof (a23_strip_len0 (HState.zs (c_tb cx))) as SL. rewrite a23_zs_len0 in SL.
pose proof (Nat2Z.is_nonneg (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) as SL0.
(* the frame is apart from `same`'s block *)
assert (HinS : In (same, Z.of_nat (length (c_tb cx)) + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym KP)); apply in_or_app; right; cbn [In]; tauto).
assert (HFS : crt_F cx + 512 <= same \/ same + Z.of_nat (length (c_tb cx)) + 1 <= crt_F cx).
{ pose proof (sep_block_frame tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md3 same _ 3 (c_pos cx)
    (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU) HinS Hin3) as Hd.
  pose proof HJ as (_ & Hly & _). rewrite (crt_F_ly cx _ ly3 Hly), crt_frame3 in Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Rn : req_size (Z.of_nat (length (c_tb cx)) + 1) = Z.of_nat (length (c_tb cx)) + 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (c_tb cx)) + 1) 0); lia).
  rewrite Rn in Hd. lia. }
(* the store's byte is the only memory the run moved below the ceiling *)
set (E1 := ewset E 51 v51) in *.
assert (EA51 : bv_unsigned (ew E1 51) = same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))))
  by (unfold E1; rewrite ew_ewset_same; exact EV51).
assert (HE1 : crt_E cx E1) by exact (a23_E_agree cx E E1 (env_agree_ewset E 51 v51) HE).
pose proof HE1 as (E2v & E3v & E4v & E8v & E9v & E26v & EXv).
assert (HSBX : forall a, 0 <= a < alloc_ceiling ->
  a <> same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) ->
  ms_mem ms (Z_to_bv 64 a) = ms_mem ms3 (Z_to_bv 64 a)).
{ intros a Ha Hne. apply HF. rewrite (wz a ltac:(lia)). intros (rg & Hin & Hrg). cbn [In ss_mem a23_tok28] in Hin.
  vm_compute in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [a23_wr crt_s0_region fs_ret_s0_region crt_slot_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    first [rewrite EA51 in Hrg | rewrite E8v in Hrg | rewrite E9v in Hrg]; lia. }
assert (MBX : forall a, 0 <= a < alloc_ceiling ->
  a <> same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) ->
  mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) a)
  by (intros a Ha Hne; apply a23_mb_of_raw; exact (HSBX a Ha Hne)).
(* env facts across the run *)
assert (AG : forall n, (n < 51)%nat -> ew E2 n = ew E n).
{ intros n Hn. rewrite (HAG2 n ltac:(lia)). unfold E1. apply ew_ewset_other. lia. }
assert (AS : forall (q : bv 5) (n : nat), (n < 51)%nat ->
  sr_get (ss_regs (crt_ss_ret 0x82180 crt_cs1 crt_csF)) q = SOff n 0 -> sr_get (ss_regs SS) q = SOff n 0 ->
  YK11.getr (ms_regs ms) q = YK11.getr (ms_regs ms3) q).
{ intros q n Hn H1 H2. rewrite (crt_reg_atom E2 (w_H W3) ms SS q n HS2 H2), (AG n Hn).
  symmetry. exact (crt_reg_atom E (w_H W3) ms3 _ q n HS H1). }
assert (HR : forall r : bv 5, In r [19; 20; 21; 22; 23; 24; 26; 27]%bv ->
  YK11.getr (ms_regs ms) r = YK11.getr (ms_regs ms3) r).
{ intros r Hr. assert (Hr' : In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) by (cbn [In] in Hr |- *; tauto).
  pose proof (RG r Hr') as X. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
    [ exact (AS 19%bv 19%nat ltac:(lia) ltac:(vm_compute; reflexivity) X)
    | exact (AS 20%bv 20%nat ltac:(lia) ltac:(vm_compute; reflexivity) X)
    | exact (AS 21%bv 21%nat ltac:(lia) ltac:(vm_compute; reflexivity) X)
    | exact (AS 22%bv 22%nat ltac:(lia) ltac:(vm_compute; reflexivity) X)
    | exact (AS 23%bv 23%nat ltac:(lia) ltac:(vm_compute; reflexivity) X)
    | exact (AS 24%bv 24%nat ltac:(lia) ltac:(vm_compute; reflexivity) X)
    | exact (AS 26%bv 26%nat ltac:(lia) ltac:(vm_compute; reflexivity) X)
    | exact (AS 27%bv 27%nat ltac:(lia) ltac:(vm_compute; reflexivity) X) ]. }
(* the NUL the store wrote *)
assert (HNUL : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms))
  (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) 1 0).
{ pose proof (fsw_region_nth E2 _ _ 0 _ HS2 N0) as (_ & _ & _ & Hc).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hc.
  rewrite (HAG2 51%nat ltac:(lia)), EA51 in Hc.
  pose proof (proj1 (Forall_forall _ _) Hc _ (or_introl eq_refl) 0 ltac:(cbn; lia)) as (b & Hb & Hm).
  intros kk Hk. destruct kk as [|kk]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
  cbn [YP09.c_off] in Hm. rewrite !Z.add_0_r in Hm. rewrite Hm. f_equal.
  cbn in Hb. injection Hb as <-. apply bv_eq. vm_compute. reflexivity. }
destruct (a23_run1_post cx same k ly3 S3 U3 W3 ms3 ms HF4096 HFceil MBX HNUL HG HR HK HK7 IZS HFO HFS)
  as (HK1 & HK71 & HZS1 & HFO1).
split; [exact HK1|]. split; [exact HK71|]. split; [exact HZS1|]. split; [exact HFO1|].
split.
{ rewrite (AS 25%bv 25%nat ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(exact (RG 25%bv ltac:(cbn [In]; tauto)))). exact I25. }
split.
{ rewrite (crt_reg_atom E2 (w_H W3) ms SS 18%bv 48 HS2 (RG 18%bv ltac:(cbn [In]; tauto))), (AG 48%nat ltac:(lia)),
    (crt_E_text cx E HE). reflexivity. }
split.
{ pose proof (fsw_region_nth E2 _ _ 1 _ HS2 N1) as (_ & _ & _ & Hc).
  cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hc.
  rewrite (AG 8%nat ltac:(lia)) in Hc. pose proof HE as (_ & _ & _ & E8 & _). rewrite E8 in Hc. exact Hc. }
split.
{ pose proof (fsw_region_nth E2 _ _ 2 _ HS2 N2) as (_ & _ & _ & Hc).
  cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hc.
  rewrite (AG 9%nat ltac:(lia)) in Hc. pose proof HE as (_ & _ & _ & _ & E9 & _). rewrite E9 in Hc. exact Hc. }
{ pose proof (fsw_region_nth E _ _ 2 (crt_frame_region crt_csF) HS eq_refl) as (_ & _ & _ & Hc).
  cbn [crt_frame_region YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hc.
  assert (EFv : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
  rewrite EFv in Hc.
  apply (crt_chunks_env E E2); [intros n Hn; apply AG; lia | exact a23_csF_atoms|].
  apply (a23_chunks_mb E (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) _ _ 504 512
    a23_csF_off); [|exact Hc].
  intros a Ha. apply MBX; lia. }
Qed.


(* ================= segments 8-9, B 0x82180 -> 0x821c4: the from-lemma of this lane's second piece ================= *)
Lemma a23_seg89 :
  crt_from SK B (crt_ss_ret 0x821c4 crt_cs1 crt_csF) (crt_INV_82068 B) ->
  crt_from SK B (crt_ss_ret 0x82180 crt_cs1 crt_csF) (a23_and crt_INV_82028 (crt_R7 B)).
Proof.
intros NEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HINV as (HI28 & HR7). destruct HR7 as (same & HK & HK7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof HK as HK'.
destruct HK' as (K20r & K21r & K24r & KP & KU & KH & K7 & K8 & K9 & Ks1 & Ks2 & HX1 & HX2 & HI1 & HI2 & KF1 & KF2
  & K12 & K13 & K14 & K15 & Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kp1 & Kp2 & Kwlo & Kwu & Ksh1 & Ksh2 & KRA).
cbn zeta in K24r, Ks1, Ks2, K12, HX1, HX2.
pose proof HI28 as HI28'.
destruct HI28' as (same0 & I25 & I13 & I11 & I24 & I18 & I14 & I16 & I12 & I15 & IZS & IZT & Is1 & Is2).
cbn zeta in I11.
pose proof (a23_strip_len0 (HState.zs (c_tb cx))) as SL. rewrite a23_zs_len0 in SL.
pose proof (Nat2Z.is_nonneg (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) as SL0.
pose proof HJ as HJ0. pose proof HARU as HARU0.
assert (HTXb : 0 <= c_text cx < 2 ^ 64).
{ pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)).
  pose proof HACV as HACV'. vm_compute YM05.CEIL_MAX in HACV'.
  unfold HEAD, FSH_Fn_writer.enc_size in HX1, HX2. lia. }
set (v51 := Z_to_bv 64 (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))))).
assert (EV51 : bv_unsigned v51 = same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))))
  by (unfold v51; apply wz; lia).
assert (EA11 : bv_unsigned (ew (ewset E 51 v51) 11) = Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))).
{ rewrite ew_ewset_other by lia.
  rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 11%bv 11 HS ltac:(vm_compute; reflexivity)), I11.
  unfold w64. apply wz. vm_compute YM05.CEIL_MAX in HACV. lia. }
destruct (Z.eq_dec (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) mod 4) 0) as [Hm0|Hm1].
- (* the mod-4 arm: first strcmp (text, same) *)
  set (C := BC_EQ).
  assert (HC : branch_taken C (sv_denot (ewset E 51 v51) (SAlu ALU_AND (SOff 11 0) (SLit 3)))
    (sv_denot (ewset E 51 v51) (SLit 0)) = true)
    by (unfold C; rewrite (a23_mod4_bt _ _ EA11 SL0), Hm0; reflexivity).
  destruct (a23_st28 C cx E k ly3 S3 U3 W3 ms3 md3 same v51 HB HE HI28 HK HARU K24r EV51 HC HS) as (HS1 & SHOK).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK fs_Bspan PC_strcmp.
  { eapply (awr_ok_cons_gen tfibsegs B (ewset E 51 v51) (a23_wr 51) _ _ _ _ _ _ _ _ _ 51%nat
      (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) ltac:(reflexivity)
      ltac:(rewrite ew_ewset_same; exact EV51)).
    - intros a Ha. cbn [a23_wr YP09.r_wlo YP09.r_whi] in Ha.
      exact (proj2 (K12 a ltac:(lia))).
    - exact (a23_awr2 B cx (ewset E 51 v51) ly3 S3 crt_cs1 HB
        (a23_E_agree cx E _ (env_agree_ewset E 51 v51) HE)). }
  match type of HS1 with st_ok _ ?EE ?SS _ => set (E2 := EE) in *; set (SS2 := SS) in * end.
  assert (AGa : forall n, (n < 51)%nat -> ew E2 n = ew E n).
  { intros n Hn. unfold E2. repeat (rewrite ew_ewset_other; [|lia]). reflexivity. }
  assert (AGb : ew E2 51 = v51).
  { unfold E2. repeat (rewrite ew_ewset_other; [|lia]). apply ew_ewset_same. }
  assert (HAG2 : forall n, (n <= 51)%nat -> ew E2 n = ew (ewset E 51 v51) n).
  { intros n Hn. destruct (Nat.eq_dec n 51) as [->|Hne]; [rewrite AGb; symmetry; apply ew_ewset_same|].
    rewrite (AGa n ltac:(lia)). symmetry. apply ew_ewset_other. exact Hne. }
  assert (HE2 : crt_E cx E2).
  { apply (a23_E_agree cx E E2); [split; [intros i Hi; exact (AGa i Hi) | unfold E2; rewrite ?ed_ewset; reflexivity]
          | exact HE]. }
  destruct (a23_post28 C cx E k ly3 S3 U3 W3 ms3 md3 ms same v51 E2 SS2 HB HE EV51 HJ0 HARU0 HFO HI28 HK HK7
    K24r HS HAG2 HF HG HS1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)
    ltac:(intros q Hq; cbn [In] in Hq;
          repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]); destruct Hq))
    as (HK1 & HK71 & HZS1 & HFO1 & G25 & G18 & HSV & HCS1 & HCSF).
  assert (Ena : bv_unsigned (ew E2 48) = c_text cx)
    by (rewrite (AGa 48%nat ltac:(lia)), (crt_E_text cx E HE); apply wz; exact HTXb).
  assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 PC_strcmp) (ms_mem ms) (seg_rom tfibsegs))
    by (apply (crt_mkst (w_H W3) _ _ ms HS1); reflexivity).
  rewrite Ems in HS1, HK1, HK71, HFO1 |- *.
  assert (Enb : bv_unsigned (ew E2 24) = same).
  { rewrite (AGa 24%nat ltac:(lia)), <- (crt_reg_atom E (w_H W3) ms3 _ 24%bv 24 HS ltac:(vm_compute; reflexivity)),
      K24r. unfold w64. apply wz. lia. }
  refine (a23_eq1 SK B RT IMG SS2 48%nat 24%nat cx E2 k ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) _ same NEXT HB HE2 Hm0
    _ _ _ _ _ _ _ _ _ Ena Enb HS1 HJ HARU HFO1 HK1 HK71 HZS1 G25 G18 HSV HCS1 HCSF);
    vm_compute; reflexivity.
- (* the other arm: straight to the second strcmp *)
  set (C := BC_NE).
  assert (HC : branch_taken C (sv_denot (ewset E 51 v51) (SAlu ALU_AND (SOff 11 0) (SLit 3)))
    (sv_denot (ewset E 51 v51) (SLit 0)) = true).
  { unfold C. change BC_NE with (neg_bc BC_EQ). rewrite branch_taken_neg, (a23_mod4_bt _ _ EA11 SL0).
    destruct (Z.eqb_spec (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx)))) mod 4) 0); [lia|].
    reflexivity. }
  destruct (a23_st28 C cx E k ly3 S3 U3 W3 ms3 md3 same v51 HB HE HI28 HK HARU K24r EV51 HC HS) as (HS1 & SHOK).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK fs_Bspan PC_strcmp.
  { eapply (awr_ok_cons_gen tfibsegs B (ewset E 51 v51) (a23_wr 51) _ _ _ _ _ _ _ _ _ 51%nat
      (same + Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) ltac:(reflexivity)
      ltac:(rewrite ew_ewset_same; exact EV51)).
    - intros a Ha. cbn [a23_wr YP09.r_wlo YP09.r_whi] in Ha.
      exact (proj2 (K12 a ltac:(lia))).
    - exact (a23_awr2 B cx (ewset E 51 v51) ly3 S3 crt_cs1 HB
        (a23_E_agree cx E _ (env_agree_ewset E 51 v51) HE)). }
  match type of HS1 with st_ok _ ?EE ?SS _ => set (E2 := EE) in *; set (SS2 := SS) in * end.
  assert (AGa : forall n, (n < 51)%nat -> ew E2 n = ew E n).
  { intros n Hn. unfold E2. repeat (rewrite ew_ewset_other; [|lia]). reflexivity. }
  assert (AGb : ew E2 51 = v51).
  { unfold E2. repeat (rewrite ew_ewset_other; [|lia]). apply ew_ewset_same. }
  assert (HAG2 : forall n, (n <= 51)%nat -> ew E2 n = ew (ewset E 51 v51) n).
  { intros n Hn. destruct (Nat.eq_dec n 51) as [->|Hne]; [rewrite AGb; symmetry; apply ew_ewset_same|].
    rewrite (AGa n ltac:(lia)). symmetry. apply ew_ewset_other. exact Hne. }
  assert (HE2 : crt_E cx E2).
  { apply (a23_E_agree cx E E2); [split; [intros i Hi; exact (AGa i Hi) | unfold E2; rewrite ?ed_ewset; reflexivity]
          | exact HE]. }
  destruct (a23_post28 C cx E k ly3 S3 U3 W3 ms3 md3 ms same v51 E2 SS2 HB HE EV51 HJ0 HARU0 HFO HI28 HK HK7
    K24r HS HAG2 HF HG HS1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)
    ltac:(intros q Hq; cbn [In] in Hq;
          repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]); destruct Hq))
    as (HK1 & HK71 & HZS1 & HFO1 & G25 & G18 & HSV & HCS1 & HCSF).
  assert (Ena : bv_unsigned (ew E2 48) = c_text cx)
    by (rewrite (AGa 48%nat ltac:(lia)), (crt_E_text cx E HE); apply wz; exact HTXb).
  assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 PC_strcmp) (ms_mem ms) (seg_rom tfibsegs))
    by (apply (crt_mkst (w_H W3) _ _ ms HS1); reflexivity).
  rewrite Ems in HS1, HK1, HK71, HFO1 |- *.
  refine (a23_cmp2 SK B RT IMG SS2 48%nat cx E2 k ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) _ same NEXT HB HE2
    _ _ _ _ _ _ _ _ _ Ena HS1 HJ HARU HFO1 HK1 HK71 HZS1 G25 G18 HSV HCS1 HCSF);
    vm_compute; reflexivity.
Qed.
End seg89.
