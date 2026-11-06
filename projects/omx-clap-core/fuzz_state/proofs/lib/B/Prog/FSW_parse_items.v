(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) walk of parse_items, in the stage form of
   lib/B/Prog/FSW_pj_set.v (this branch). B-local copies of A-kit helpers with no B twin, each copied from
   a working branch be9ecc0b1fd proofs/omx-clap-core/fuzz_state/lib/A/FSW_parse_items.v (a Theorem Labs lane):
   the writer-text facts pi_concat_cons / pi_concat_app / pi_concat_single / pi_wt_len2 / pi_wt_head / pi_rest_len /
   pi_p1_lt_end / pi_mgo / pi_obj_pieces / pi_obj_nil / pi_obj_cons / pi_spieces_head / pi_ws_repeat / pi_wind_ws,
   pi_nth_repeat / pi_zero_val, pi_stack_cells8 / pi_RA_stack (themselves A/ACex.v:322 / :330), and the entry state
   pi_q_region / pi_v_region / pi_rs / pi_gf / pi_SH with pitems_entry's proof of it; image values re-read from B
   (A_parse_items 0x84e70, FRAME_parse_items 144 = the prologue `addi sp, sp, -0x90`, the run's stop A_skip_ws 0x83598,
   ra 0x84f5c, the frame offsets of the thirteen saved registers -8 .. -104, all MEASURED on image B by the engine run
   recorded at each stage).
   Proof style as the A walk; B's code is not A's: B CALLS skip_ws at four sites (A inlines the white-space loops), so
   B's stages cut at those calls, and B's UBSan checks (one trap, the unimp 0x853d8) sit between them. *)
(* The ASan + UBSan walk of parse_items (fs.asan-ubsan 0x84e70, pf.c:211-264) against
   lib/B/FSH_Fn_reader.parse_items_spec k: STAGES.
   rule 24: proved new on image B (a Theorem Labs lane's lookup, CONFIRM 08:0xZ: no released proof of parse_items on any ASan image of
   fuzz_state; 0x84e70 appears only in statement / table files).
   STAGE A (pi_stageA): entry 0x84e70 .. entering skip_ws (q) from 0x84f58, ra 0x84f5c. MEASURED: the engine's token run
   decides every branch of the segment itself - the UBSan checks 0x84ea8 (v = 0), 0x84eb8 (v mod 8), 0x84eec (q mod 8),
   0x84f0c (in->depth + 1 overflow), 0x84f44 (in->p + 1 <= 1), the depth bound 0x84f24 (> 32), and the shadow checks
   of v (0x84ed8), q + 16 (0x84f00, 0x84f14) and q (0x84f34, 0x84f4c), all COVERED by the two shadow entries pi_SH -
   with no token, no obligation and no reservation, and stops at skip_ws's entry (FSW_parse_items_tbl.v's table holds
   the segment). It stores type 6 at v (0x84ee8), in->depth := d + 1 (0x84f18) and in->p := p + 1 (0x84f50), and
   leaves s0 = q + 16, s1 = q, s2 = 1, s3 = v, s9 = shadow (q + 16), s10 = SHADOW_OFF, s11 = shadow (q).
   Named premise: FsShadowSyms B (lib/B/FSH_Base.v, the shadow-base cells 0x9fc10 / 0xa8438 of image B).
   SINK: each Section binds (SK : YI16.sink_head) explicitly and every statement passes it with @. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_rd FSW_pj FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_parse_items_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= model-side facts of the writer text (copied from the A walk, see the header) ================= *)
Lemma pi_concat_cons : forall (x : list Z) (l : list (list Z)), concat (x :: l) = x ++ concat l.
Proof. reflexivity. Qed.
Lemma pi_concat_app : forall (l1 l2 : list (list Z)), concat (l1 ++ l2) = concat l1 ++ concat l2.
Proof.
induction l1 as [|x l1 IH]; intros l2; [reflexivity|].
cbn [app concat]. rewrite IH, app_assoc. reflexivity.
Qed.
Lemma pi_concat_single : forall (x : list Z), concat [x] = x.
Proof. intros x. cbn [concat]. apply app_nil_r. Qed.
Lemma pi_wt_len2 : forall (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  (2 <= length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr dd)))%nat.
Proof.
intros ms pr dd. cbn [WriterValue.wvpieces].
rewrite pi_concat_cons, !pi_concat_app, !pi_concat_single, !length_app. cbn [length]. lia.
Qed.
Lemma pi_wt_head : forall (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  nth_error (concat (WriterValue.wvpieces (PjTree.JObj ms) pr dd)) 0 = Some 123.
Proof. intros ms pr dd. cbn [WriterValue.wvpieces]. rewrite pi_concat_cons. reflexivity. Qed.
Lemma pi_rest_len : forall m q text len p d (tb : list byte),
  PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  Z.of_nat (length (ReaderRes.rest_at tb text p)) = text + len - p.
Proof.
intros m q text len p d tb H.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ H) as (_ & _ & _ & (Hp1 & Hp2) & _ & _ & Hlen & _).
unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn.
pose proof (Z2Nat.id (p - text) ltac:(lia)) as Hid. lia.
Qed.
Lemma pi_p1_lt_end : forall m q text len p d (tb : list byte) ms pr dd rest,
  PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr dd) ++ rest ->
  p + 1 < text + len.
Proof.
intros m q text len p d tb ms pr dd rest H HR.
pose proof (pi_rest_len m q text len p d tb H) as HL.
rewrite HR, length_app in HL. pose proof (pi_wt_len2 ms pr dd) as H2. lia.
Qed.
Fixpoint pi_mgo (pr : bool) (dd : Z) (i : nat) (l : list (list Z * PjTree.jv)) {struct l} : list (list Z) :=
  match l with
  | [] => []
  | (kk, x) :: r =>
      WriterValue.wcomma i ++ WriterValue.wind pr (dd + 1) ++ WriterSpec.spieces kk
      ++ [WriterValue.wsep pr] ++ WriterValue.wvpieces x pr (dd + 1) ++ pi_mgo pr dd (S i) r
  end.
Lemma pi_obj_pieces : forall (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  WriterValue.wvpieces (PjTree.JObj ms) pr dd =
  [123] :: pi_mgo pr dd 0 ms ++ (match ms with [] => [] | _ :: _ => WriterValue.wind pr dd end) ++ [[125]].
Proof.
intros ms pr dd. cbn [WriterValue.wvpieces]. f_equal. f_equal.
generalize 0%nat. induction ms as [|[kk x] ms IH]; intros n; [reflexivity|].
cbn [pi_mgo]. rewrite IH. reflexivity.
Qed.
Lemma pi_obj_nil : forall (pr : bool) (dd : Z),
  concat (WriterValue.wvpieces (PjTree.JObj []) pr dd) = [123; 125].
Proof.
intros pr dd. rewrite pi_obj_pieces. cbn [pi_mgo app].
rewrite pi_concat_cons, pi_concat_single. reflexivity.
Qed.
Lemma pi_obj_cons : forall kk x (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  concat (WriterValue.wvpieces (PjTree.JObj ((kk, x) :: ms)) pr dd) =
  123 :: concat (WriterValue.wind pr (dd + 1)) ++ concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr
       ++ concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (pi_mgo pr dd 1 ms)
       ++ concat (WriterValue.wind pr dd) ++ [125].
Proof.
intros kk x ms pr dd. rewrite pi_obj_pieces. cbn [pi_mgo WriterValue.wcomma].
rewrite pi_concat_cons, !pi_concat_app, !pi_concat_single.
cbn [app]. rewrite !app_assoc. reflexivity.
Qed.
Lemma pi_spieces_head : forall kk : list Z,
  concat (WriterSpec.spieces kk) = 34 :: concat (WriterSpec.spieces_run [] kk) ++ [34].
Proof.
intros kk. unfold WriterSpec.spieces.
rewrite pi_concat_cons, pi_concat_app, pi_concat_single. reflexivity.
Qed.
Lemma pi_ws_repeat : forall n, Forall (fun c => PjGrammar.ws c = true) (concat (repeat [32; 32] n)).
Proof.
induction n as [|n IH]; [constructor|].
cbn [repeat]. rewrite pi_concat_cons. apply Forall_app. split; [|exact IH].
repeat constructor.
Qed.
Lemma pi_wind_ws : forall (pr : bool) (dd : Z),
  Forall (fun c => PjGrammar.ws c = true) (concat (WriterValue.wind pr dd)).
Proof.
intros pr dd. unfold WriterValue.wind. destruct pr; [|constructor].
rewrite pi_concat_cons. apply Forall_app. split; [repeat constructor | apply pi_ws_repeat].
Qed.
Lemma pi_nth_repeat : forall (A : Type) (x : A) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof. intros A x n. induction n as [|n IH]; intros [|i] H; cbn; try lia; [reflexivity | apply IH; lia]. Qed.
Lemma pi_zero_val : forall m v off n, PjStruct.pj_zero tfibsegs m v -> 0 <= off -> off + Z.of_nat n <= 56 ->
  val_mem tfibsegs m (v + off) n 0.
Proof.
intros m v off n (_ & (_ & _ & HB)) Hoff Hn k Hk.
pose proof (HB (Z.to_nat (off + Z.of_nat k)) ltac:(rewrite repeat_length; lia)) as Hx.
rewrite Z2Nat.id in Hx by lia. rewrite pi_nth_repeat in Hx by lia.
replace (v + off + Z.of_nat k) with (v + (off + Z.of_nat k)) by lia.
assert (L0 : YO0f.le_byte 0 n k = 0).
{ unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
rewrite L0. exact Hx.
Qed.
Lemma pi_stack_cells8 : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + 8 <= hi ->
  lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi x Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C. split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C.
  replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia.
  apply Z_mod_mult.
Qed.

(* ================= the entry state (A's pitems_entry state, B's numbering is the same) ================= *)
(* struct pj_in at a0: p at 0, in->end at 8, in->depth at 16 *)
Definition pi_q_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 0)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))].
(* the result object at a1, zeroed by the caller: type (4 bytes at 0) and the six words at 8 .. 48 as chunks *)
Definition pi_v_region : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 56 0 56
    [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
     YP09.mkChunk 24 (CVal 8 (SLit 0)); YP09.mkChunk 32 (CVal 8 (SLit 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
     YP09.mkChunk 48 (CVal 8 (SLit 0))].
Definition pi_rs : list YP09.region := [pi_q_region; pi_v_region].
Definition pi_gf : list (nat * afact) :=
  [(10%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (11%nat, mkAF 4096 (2 ^ 47 - 56) 3);
   (12%nat, mkAF 1 1 0);
   (xatom 0, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 1, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
   (xatom 2, mkAF 0 1 0)].
Definition pi_ss0 : sstate := fss0T_args A_parse_items FRAME_parse_items pi_rs pi_gf.
Definition pi_SH : list shent := [mkSHE 10 0 24; mkSHE 11 0 56].
Definition pi_xs (p e d : Z) : list word := [Z_to_bv 64 p; Z_to_bv 64 e; Z_to_bv 64 d].
Lemma pi_regions_wf : regions_wf (fsT_regions_args FRAME_parse_items pi_rs) = true.
Proof. vm_compute. reflexivity. Qed.

(* the frame parse_items' prologue writes (0x84e74 .. 0x84ea4): ra, s0 .. s11 at entry sp - 8 .. entry sp - 104 *)
Definition pi_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv); (-64, 22%bv);
   (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].
Definition pi_frame (m : word -> option byte) (sp : Z) (regs0 : bvmap 5 word) : Prop :=
  Forall (fun p => val_mem tfibsegs m (sp + fst p) 8 (bv_unsigned (YK11.getr regs0 (snd p)))) pi_saved.
(* the shadow cell of an address, as the code computes it (`srli x, a, 3; add x, x, s10`) *)
Definition pi_sh (a : Z) : Z := a / 8 + SHADOW_OFF.

(* what stage A establishes at the call of skip_ws (q) 0x84f58: the argument and return registers, the registers the walk
   reads after the call (s0 = q + 16, s1 = q, s2 = 1, s3 = v, s9 = shadow (q + 16), s10 = SHADOW_OFF,
   s11 = shadow (q)), the untouched callee-saved ones, the frame *)
Definition pi_callA (W : world tfibsegs) (regs regsC : bvmap 5 word) (memC : word -> option byte) (q v : Z) : Prop :=
  YK11.getr regsC 1 = w64 0x84f5c /\ spZ regsC = spZ regs - 144 /\ YK11.getr regsC 10 = w64 q /\
  YK11.getr regsC 8 = w64 (q + 16) /\ YK11.getr regsC 9 = w64 q /\ YK11.getr regsC 18 = w64 1 /\
  YK11.getr regsC 19 = w64 v /\ YK11.getr regsC 25 = w64 (pi_sh (q + 16)) /\
  YK11.getr regsC 26 = w64 SHADOW_OFF /\ YK11.getr regsC 27 = w64 (pi_sh q) /\
  Forall (fun r => YK11.getr regsC r = YK11.getr regs r) [3; 4; 20; 22; 23; 24]%bv /\
  pi_frame (mrestrict (w_H W) memC) (spZ regs) regs.
(* ... and the memory there: in->p = p + 1, in->depth = d + 1, type 6 at v, v's six words still zero, every byte outside
   the frame, struct pj_in and v unchanged *)
Definition pi_memA (W : world tfibsegs) (mem memC : word -> option byte) (sp q v p e d : Z) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) memC) q 8 (p + 1) /\ val_mem tfibsegs (mrestrict (w_H W) memC) (q + 8) 8 e /\
  val_mem tfibsegs (mrestrict (w_H W) memC) (q + 16) 4 (d + 1) /\
  val_mem tfibsegs (mrestrict (w_H W) memC) v 4 6 /\
  Forall (fun o => val_mem tfibsegs (mrestrict (w_H W) memC) (v + o) 8 0) [8; 16; 24; 32; 40; 48] /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 144 <= x < sp) -> ~ (q <= x < q + 24) -> ~ (v <= x < v + 56) ->
     memC (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) memC).

(* a register of the stopped run, as the symbolic state says (FSW_pj_set.v's gw_reg / gw_val) *)
Ltac pi_gw_reg HS r :=
  rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ r HS);
  lazymatch goal with |- sv_denot _ (sr_get ?l ?q) = _ =>
    let e := eval vm_compute in (sr_get l q) in change (sr_get l q) with e end.
Ltac pi_gw_val :=
  apply bv_eq; unfold w64; rewrite unsigned_lit_small by (unfold pi_sh, SHADOW_OFF in *; lia);
  lazymatch goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (YP0e.U E e) end.

(* the shadow cell of an atom's address, as the engine writes it *)
Lemma pi_U_shadow : forall E n c a, ew E n = Z_to_bv 64 a -> 0 <= a -> 0 <= c -> a + c < 2 ^ 47 ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  YP0e.U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0)) = pi_sh (a + c).
Proof.
intros E n c a Hn Ha Hc Hac H32.
rewrite U_SAlu. rewrite (U_SAlu E ALU_SRL). cbn [zalu_raw].
rewrite (U_atom_off E n a c Hn) by lia.
rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; lia). rewrite U_lit by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (D1 : 0 <= (a + c) / 8 <= a + c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
unfold pi_sh. rewrite (zcanon_small ((a + c) / 8)) by lia.
apply zcanon_small. unfold SHADOW_OFF. lia.
Qed.

(* ================= the resume state after a call (FSW_ret's fss_retT, B's numbering) =================
   MEASURED (engine, this branch): at every resume of parse_items the frame [sp0 - 144, sp0) holds the thirteen saved
   registers at offsets 40 .. 136 (ra at 136, s0 at 128, ... s11 at 40), the extra atoms are
   xatom 0 / 1 / 2 = in->p / in->end / in->depth at the resume, xatom 3 .. 15 = the ENTRY ra and s0 .. s11 (what the
   epilogue reloads, in pi_saved_regs order), xatom 16 .. 19 = v's kids / keys / n / cap; the object regions are
   struct pj_in at atom 9 = s1 = q and the result object at atom 19 = s3 = v. *)
Definition pi_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition pi_xsR (p e d : Z) (regs0 : bvmap 5 word) (kids keys n cap cb : Z) : list word :=
  map (Z_to_bv 64) [p; e; d] ++ map (YK11.getr regs0) pi_saved_regs ++ map (Z_to_bv 64) [kids; keys; n; cap; cb].
Definition pi_cs : list YP09.chunk :=
  [YP09.mkChunk 136 (CVal 8 (SOff (xatom 3) 0)); YP09.mkChunk 128 (CVal 8 (SOff (xatom 4) 0));
   YP09.mkChunk 120 (CVal 8 (SOff (xatom 5) 0)); YP09.mkChunk 112 (CVal 8 (SOff (xatom 6) 0));
   YP09.mkChunk 104 (CVal 8 (SOff (xatom 7) 0)); YP09.mkChunk 96 (CVal 8 (SOff (xatom 8) 0));
   YP09.mkChunk 88 (CVal 8 (SOff (xatom 9) 0)); YP09.mkChunk 80 (CVal 8 (SOff (xatom 10) 0));
   YP09.mkChunk 72 (CVal 8 (SOff (xatom 11) 0)); YP09.mkChunk 64 (CVal 8 (SOff (xatom 12) 0));
   YP09.mkChunk 56 (CVal 8 (SOff (xatom 13) 0)); YP09.mkChunk 48 (CVal 8 (SOff (xatom 14) 0));
   YP09.mkChunk 40 (CVal 8 (SOff (xatom 15) 0))].
Definition pi_qR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 0)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))].
Definition pi_vR : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 56 0 56
    [YP09.mkChunk 0 (CVal 4 (SLit 6)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 16) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 17) 0));
     YP09.mkChunk 40 (CVal 8 (SOff (xatom 18) 0)); YP09.mkChunk 48 (CVal 8 (SOff (xatom 19) 0))].
Definition pi_gfR : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (19%nat, mkAF 4096 (2 ^ 47 - 56) 3);
   (xatom 0, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 1, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
   (xatom 2, mkAF 1 2 0)].
(* the shadow-cell expression the code keeps in s9 / s11 (and later s7 / s8) *)
Definition pi_shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0).
(* the cursor byte, as a region based at the in->p atom; its VALUE is the env atom xatom 20, never a Rocq variable
   (a variable inside the symbolic state stops the engine's branch on the byte from reducing) *)
Definition pi_byte : YP09.region :=
  YP09.mkRegion (Some (xatom 0)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (xatom 20) 0))].
Definition pi_SHR : list shent := [mkSHE 9 0 24; mkSHE 19 0 56; mkSHE (xatom 0) 0 1].
(* the plain resume state at 0x84f5c (after the first skip_ws) *)
Definition pi_ssB0 : sstate := fss_retT 0x84f5c 144 pi_cs [pi_qR; pi_vR] pi_gfR.
(* the extra atoms of a resume env, by index *)
Lemma pi_xsR_nth : forall p e d regs0 kids keys n cap cb,
  let xs := pi_xsR p e d regs0 kids keys n cap cb in
  nth 0 xs (Z_to_bv 64 0) = Z_to_bv 64 p /\ nth 1 xs (Z_to_bv 64 0) = Z_to_bv 64 e /\
  nth 2 xs (Z_to_bv 64 0) = Z_to_bv 64 d /\
  (forall j, (j < 13)%nat -> nth (3 + j) xs (Z_to_bv 64 0) = YK11.getr regs0 (nth j pi_saved_regs 0%bv)) /\
  nth 16 xs (Z_to_bv 64 0) = Z_to_bv 64 kids /\ nth 17 xs (Z_to_bv 64 0) = Z_to_bv 64 keys /\
  nth 18 xs (Z_to_bv 64 0) = Z_to_bv 64 n /\ nth 19 xs (Z_to_bv 64 0) = Z_to_bv 64 cap /\
  nth 20 xs (Z_to_bv 64 0) = Z_to_bv 64 cb.
Proof.
intros p e d regs0 kids keys n cap cb xs. subst xs. unfold pi_xsR, pi_saved_regs. cbn [map app].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ intros j Hj. do 13 (destruct j as [|j]; [reflexivity|]). lia. }
repeat split; reflexivity.
Qed.


Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.

(* A/ACex.v:330 RA_stack, copied (via the A walk's pi_RA_stack) *)
Lemma pi_RA_stack : forall ly S (W : world tfibsegs) mem md x n,
  AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 ->
  8 <= n -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hhi Hx8 Hn8 Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
destruct (pi_stack_cells8 _ _ x Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.

(* the write window of the entry state (A's pi_awr_ok, over RELOC's FP-keyed core): the frame and struct pj_in inside
   the journal's window, the two shadow-base cells read-only, the object [v, v + 56) the caller's FP in a live block or
   a live fake frame *)
Lemma pi_awr_ok : forall ly S (W : world tfibsegs) mem regs q ot v xs STK FP,
  spZ regs <= q -> q + 24 <= ot -> alloc_ceiling + STK <= spZ regs -> FRAME_parse_items <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v ->
  0 <= q -> q + 24 <= 2 ^ 64 -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  pobj tfibsegs B ly S W mem v ->
  (forall a, v <= a < v + 56 -> inFP FP a) ->
  awr_ok tfibsegs B (Ereg regs (fs_extraT ++ xs)) (ss_mem pi_ss0)
    (STK + (ot - spZ regs)) ot FP (ablocks B ly S) (ablocks B ly S) ly [] (frames S).
Proof.
intros ly S W mem regs q ot v xs STK FP Hsq Hq24 Hceil HSTK H10 H11 Hq0 Hq64 Hv0 Hv64 HPO HFP.
pose proof asan_consts as (C1 & _).
set (E := Ereg regs (fs_extraT ++ xs)).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ xs) 2 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = q)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ xs) 10 10%bv eq_refl), H10;
      apply MState.unsigned_lit; lia).
assert (E11 : bv_unsigned (ew E 11) = v)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ xs) 11 11%bv eq_refl), H11;
      apply MState.unsigned_lit; lia).
assert (HF : FRAME_parse_items = 144) by reflexivity.
unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, pi_rs.
cbn [ss_mem app].
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
  [reflexivity | cbn [fstk YP09.r_base]; rewrite E2; lia
  | cbn [fstk YP09.r_wlo]; lia | cbn [fstk YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
eapply awr_ok_cons_stack_off with (n := 10%nat) (d := q - ot);
  [reflexivity | cbn [pi_q_region YP09.r_base]; rewrite E10; lia
  | cbn [pi_q_region YP09.r_wlo]; lia | cbn [pi_q_region YP09.r_whi]; lia |].
eapply awr_ok_cons_gen with (k := 11%nat) (b := v);
  [reflexivity | cbn [pi_v_region YP09.r_base]; exact E11 | | apply awr_ok_nil].
intros a Ha. cbn [pi_v_region YP09.r_wlo YP09.r_whi] in Ha.
destruct HPO as [[((cid & pos & Hin & Hcid & Hal & H1 & H2) & _ & _) | ((b & m & Hin & H1 & H2) & _ & _)] _].
- right. right. split; [apply HFP; lia|]. exists cid, pos. split; [exact Hin|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
- left. right. left. split; [apply HFP; lia|]. exists b, m. split; [exact Hin | unfold HEAD in *; lia].
Qed.

(* ---- the entry state of the walk (A's pitems_entry over B's names) ---- *)
Theorem pi_entry :
  forall ly S Us (W : world tfibsegs) regs mem md ch FP q ot v text len p (tb : list byte) tcap d STK,
  afn_preU tfibsegs B STK ly S Us W regs mem md ch ->
  FRAME_parse_items <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  0 <= d <= 1 ->
  st_ok tfibsegs (Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) pi_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs))) /\
  @ajournal rc SK tfibsegs B (STK + (ot - spZ regs)) ot FP ly S W (unpoison Us mem) md []
    ly S W (unpoison Us mem) md 0 /\
  ARU tfibsegs B ly S Us W mem md /\
  sh_ok tfibsegs fs_Bx pi_SH (Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) (mrestrict (w_H W) mem).
Proof.
intros ly S Us W regs mem md ch FP q ot v text len p tb tcap d STK HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO Hd.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_ARU B STK ly S Us W regs mem md ch HPRE) as HARU.
pose proof HPRE as (HAPRE & _ & _).
pose proof HAPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (fsw_sp B STK ly S Us W regs mem md ch HPRE) as (_ & HceilSTK & H47sp & HS0).
destruct HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
set (E := Ereg regs (fs_extraT ++ pi_xs p (text + len) d)).
assert (E10 : ew E 10 = Z_to_bv 64 q)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 1)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 12 12%bv eq_refl); exact H12).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 2 2%bv eq_refl); reflexivity).
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (EX2 : ew E (xatom 2) = Z_to_bv 64 d) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
destruct (fsw_pobj_low B ly S W (unpoison Us mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
destruct HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison Us mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
assert (Hp1 : 4096 <= p) by (unfold HEAD in *; lia).
assert (Hp2 : p <= 2 ^ 47 - 2 ^ 23) by lia.
assert (He1 : 4096 <= text + len) by (unfold HEAD in *; lia).
assert (He2 : text + len <= 2 ^ 47 - 2 ^ 23) by lia.
assert (Hqlo : ly_stk_lo ly <= q) by lia.
assert (Hqhi : q + 24 <= ly_stk_hi ly) by lia.
assert (Hq46 : 2 ^ 46 <= q) by lia.
assert (Hq47 : q <= 2 ^ 47 - 24) by lia.
assert (RQ : YP09.region_ok tfibsegs E (mrestrict (w_H W) mem) pi_q_region).
{ pose proof HIN as (Bp & Be & Bd & Bw & _).
  unfold pi_q_region, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10, (MState.unsigned_lit q) by lia.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold YP09.writable_at. destruct Bw as (_ & _ & Bw3). exact (Bw3 o ltac:(lia)).
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (fsw_pj_chunk8 tfibsegs E (mrestrict (w_H W) mem) q 0 (SOff (xatom 0) 0) p);
        [rewrite Z.add_0_r; split; [lia | exact Bp] | rewrite fsw_SOff0; exact EX0].
    + apply (fsw_pj_chunk8 tfibsegs E (mrestrict (w_H W) mem) q 8 (SOff (xatom 1) 0) (text + len));
        [split; [lia | exact Be] | rewrite fsw_SOff0; exact EX1].
    + apply (fsw_pj_chunk4 tfibsegs E (mrestrict (w_H W) mem) q 16 (SOff (xatom 2) 0) d);
        [split; [lia | exact Bd] | rewrite fsw_SOff0; exact EX2]. }
assert (RV : YP09.region_ok tfibsegs E (mrestrict (w_H W) mem) pi_v_region).
{ unfold pi_v_region, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E11, (MState.unsigned_lit v) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; exact (proj2 HPO o ltac:(lia))|].
  repeat (apply Forall_cons;
    [apply (chunk_ok_val tfibsegs E _ v _ _ (SLit 0) 0);
       [reflexivity | cbn; lia | cbn; lia | apply pi_zero_val; [exact HZERO | lia | cbn; lia]] |]).
  apply Forall_nil. }
assert (HDJ : YP09.pairwise_disjoint E (fsT_regions_args FRAME_parse_items pi_rs)).
{ apply pairwise_disjoint_of_extents.
  pose proof (fsw_pobj_off_img B ly S W (unpoison Us mem) md mem v HAR HPO) as HO.
  unfold fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, pi_rs, pi_q_region, pi_v_region,
    extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, E10, E11, (MState.unsigned_lit q) by lia. rewrite (MState.unsigned_lit v) by lia.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
  assert (HF : FRAME_parse_items = 144) by reflexivity.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (HGF : atoms_ok E pi_gf).
{ unfold pi_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E11, E12, EX0, EX1, EX2. rewrite !MState.unsigned_lit by lia.
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r.
  split; [split; [lia | split; [exact Hq8 | lia]]|].
  split; [split; [lia | split; [exact Hv8 | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [|exact I]. split; [lia | split; [apply Z.mod_1_r | lia]]. }
assert (HS : st_ok tfibsegs E pi_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs)))).
{ unfold pi_ss0.
  apply (fsw_entryT_argsX B STK FRAME_parse_items ly S Us W regs mem md ch A_parse_items pi_rs pi_gf
    (pi_xs p (text + len) d) (proj1 HSS) (proj2 HSS) HPRE ltac:(split; [vm_compute; discriminate | exact HSTK])
    pi_regions_wf); [| exact HDJ | exact HGF].
  constructor; [exact RQ | constructor; [exact RV | constructor]]. }
split; [exact HS|].
split.
{ exact (fsw_ajournal_init_ot (SK := SK) B STK FP ly S Us W regs mem md ch ot HPRE ltac:(lia) Hot16 Hotly Hpot). }
split; [exact HARU|].
unfold sh_ok, pi_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 10%nat q 24 q 0 24);
    [ apply (proj1 (fsw_ARU_stack_ra tfibsegs B (AR_laws_ok tfibsegs B) ly S Us W mem md (w_H W) q 24 HARU
        ltac:(lia) ltac:(lia)));
      exact (pi_RA_stack ly S W (unpoison Us mem) md q 24 HAR Hqlo Hqhi Hq8 ltac:(reflexivity) ltac:(lia))
    | unfold fs_Bx; apply U_atom;
      [unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity | unfold SHADOW_OFF; lia]
    | apply U_atom; [exact E10 | lia]
    | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
- apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 11%nat v 56 v 0 56);
    [ destruct HPO as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr
    | unfold fs_Bx; apply U_atom;
      [unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity | unfold SHADOW_OFF; lia]
    | apply U_atom; [exact E11 | lia]
    | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx.
  exact (fsw_pobj_off_shadow B ly S W (unpoison Us mem) md mem v HAR HPO x ltac:(lia)).
Qed.

(* ---- STAGE A: entry 0x84e70 .. entering skip_ws (q) from 0x84f58 ---- *)
Lemma pi_stageA : forall ly S U (W : world tfibsegs) regs mem md ch FP q ot v text len p (tb : list byte) tcap d STK
  (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK ly S U W regs mem md ch ->
  FRAME_parse_items <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  0 <= d <= 1 ->
  (forall a, v <= a < v + 56 -> inFP FP a) ->
  (forall regsC memC mat,
     pi_callA W regs regsC memC q v ->
     pi_memA W mem memC (spZ regs) q v p (text + len) d ->
     @ajournal rc SK tfibsegs B (STK + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S W (unpoison U memC)
       (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W memC (with_vm_backing (m_vm_lazy md) mat md) ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_skip_ws regsC memC (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP q ot v text len p tb tcap d STK Q
  HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO Hd HFP KC.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (pi_entry ly S U W regs mem md ch FP q ot v text len p tb tcap d STK
  HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO Hd) as (HS & HJ & HARU & SHOK).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof (fsw_sp B STK ly S U W regs mem md ch HPRE) as (Hal16 & HceilSTK & H47sp & HS0).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
pose proof HPRE as (HAPRE & _ & _). pose proof HAPRE as (HAR & _).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof HAPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hq47 : q <= 2 ^ 47 - 24) by lia.
set (E := Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regs r) by (intros r; subst E; apply ew_Ereg_reg).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (rewrite (ER 10%bv); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite (ER 11%bv); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (subst E; rewrite fsw_ew_xatom; reflexivity).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (subst E; rewrite fsw_ew_xatom; reflexivity).
assert (EX2 : ew E (xatom 2) = Z_to_bv 64 d) by (subst E; rewrite fsw_ew_xatom; reflexivity).
assert (HSTKf : FRAME_parse_items = 144) by reflexivity.
unfold YG0d.cfg_at. change (w64 A_parse_items) with (Z_to_bv 64 A_parse_items).
change mem with (ms_mem (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs))) in HJ at 2, HARU, SHOK.
(* ---- 0x84e70 .. 0x84f58: prologue, the UBSan / ASan checks, type 6, in->depth + 1, in->p + 1, jal skip_ws ---- *)
fsw_aj_run_to_tokU pitems_tbl_ok HS HJ HARU SHOK fs_Bspan A_skip_ws.
{ exact (pi_awr_ok ly S W mem regs q ot v (pi_xs p (text + len) d) STK FP Hsq Hq24 HceilSTK HSTK H10 H11
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPO HFP). }
pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
pose proof (fsw_region_nth _ _ _ 3 _ HS eq_refl) as HRQ.
pose proof (fsw_region_nth _ _ _ 4 _ HS eq_refl) as HRV.
cbn [ms_mem restrict] in HR0, HRQ, HRV.
assert (FR : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 144 <= x < spZ regs) -> ~ (q <= x < q + 24) ->
  ~ (v <= x < v + 56) -> ms_mem ms (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx H1 H2 H3. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?(MState.unsigned_lit x) in Hr by lia;
    first [ lia | rewrite E2 in Hr; lia | rewrite E10, (MState.unsigned_lit q) in Hr by lia; lia
          | rewrite E11, (MState.unsigned_lit v) in Hr by lia; lia ] |]); destruct Hin. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl).
apply (KC (ms_regs ms) (ms_mem ms) mat); [| | exact HJ | exact HARU].
- unfold pi_callA.
  split; [pi_gw_reg HS (1%bv : bv 5); pi_gw_val; apply U_lit; lia|].
  split; [unfold spZ at 1; rewrite (fsw_reg_off _ _ _ ms 2%bv 2 (-144) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)); lia|].
  split; [pi_gw_reg HS (10%bv : bv 5); pi_gw_val; apply U_atom; [exact E10 | lia]|].
  split; [pi_gw_reg HS (8%bv : bv 5); pi_gw_val; apply U_atom_off; [exact E10 | lia | lia]|].
  split; [pi_gw_reg HS (9%bv : bv 5); pi_gw_val; apply U_atom; [exact E10 | lia]|].
  split; [pi_gw_reg HS (18%bv : bv 5); pi_gw_val; apply U_atom; [rewrite (ER 12%bv); exact H12 | lia]|].
  split; [pi_gw_reg HS (19%bv : bv 5); pi_gw_val; apply U_atom; [exact E11 | lia]|].
  split; [pi_gw_reg HS (25%bv : bv 5); pi_gw_val; exact (pi_U_shadow E 10 16 q E10 ltac:(lia) ltac:(lia) ltac:(lia) E32)|].
  split; [pi_gw_reg HS (26%bv : bv 5); pi_gw_val; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]|].
  split; [pi_gw_reg HS (27%bv : bv 5); pi_gw_val;
          rewrite (pi_U_shadow E 10 0 q E10 ltac:(lia) ltac:(lia) ltac:(lia) E32), Z.add_0_r; reflexivity|].
  split.
  { repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ =>
      pi_gw_reg HS r; rewrite fsw_SOff0; exact (ER r) end|]). apply Forall_nil. }
  unfold pi_frame, pi_saved.
  repeat (apply Forall_cons; [cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (YK11.getr regs ?r)) =>
      apply (fsw_field _ _ 2 _ _ _ _ _ _ o 8%N (SOff (Z.to_nat (bv_unsigned r)) 0) _ HR0 E2 ltac:(cbn; tauto));
      [rewrite fsw_SOff0, ER; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]).
  apply Forall_nil.
- unfold pi_memA.
  assert (EQ : bv_unsigned (ew E 10) = q) by (rewrite E10; apply MState.unsigned_lit; lia).
  assert (EV : bv_unsigned (ew E 11) = v) by (rewrite E11; apply MState.unsigned_lit; lia).
  split.
  { replace q with (q + 0) at 1 by lia.
    apply (fsw_field _ _ 10 _ _ _ _ _ _ 0 8%N (SOff (xatom 0) 1) (p + 1) HRQ EQ ltac:(cbn; tauto));
      [apply bv_eq; rewrite denot_SOff, EX0, MState.unsigned_lit by lia; rewrite MState.unsigned_lit by lia;
       apply zcanon_id; unfold M64; lia | cbn; lia | cbn; lia]. }
  split.
  { apply (fsw_field _ _ 10 _ _ _ _ _ _ 8 8%N (SOff (xatom 1) 0) (text + len) HRQ EQ ltac:(cbn; tauto));
      [rewrite fsw_SOff0; exact EX1 | cbn; lia | cbn; lia]. }
  split.
  { apply (fsw_field _ _ 10 _ _ _ _ _ _ 16 4%N (SOff (xatom 2) 1) (d + 1) HRQ EQ ltac:(cbn; tauto));
      [apply bv_eq; rewrite denot_SOff, EX2, MState.unsigned_lit by lia; rewrite MState.unsigned_lit by lia;
       apply zcanon_id; unfold M64; lia | cbn; lia | cbn; lia]. }
  split.
  { replace v with (v + 0) at 1 by lia.
    apply (fsw_field _ _ 11 _ _ _ _ _ _ 0 4%N (SLit 6) 6 HRV EV ltac:(cbn; tauto)); [reflexivity | cbn; lia | cbn; lia]. }
  split.
  { repeat (apply Forall_cons; [lazymatch goal with |- val_mem _ _ (v + ?o) 8 0 =>
      apply (fsw_field _ _ 11 _ _ _ _ _ _ o 8%N (SLit 0) 0 HRV EV ltac:(cbn; tauto)); [reflexivity | cbn; lia | cbn; lia]
      end|]). apply Forall_nil. }
  split; [exact FR|].
  exact HG.
Qed.

End W.
(* ================= STAGE B: resume at 0x84f5c (after skip_ws #1) =================
   MEASURED (engine, both arms, K = 54, NO obligation, no reservation, sh_chk true, two token words):
   the segment reads the shadow of q (0x84f5c), computes s4 = q + 8 and s7 = shadow (q + 8) and reads its shadow
   (0x84f70), loads in->end and in->p, and decides
     0x84f80 `bgeu p, end`   NOT taken: the premise p < e (the model's text has a byte at p);
     0x84f84 `beqz p`        NOT taken: 4096 <= p (atom fact);
     0x84f94 `bnez shadow p` the cursor's shent decides it (the byte is addressable);
     0x84f9c `beqz s2`       NOT taken: s2 = 1, the object flag folded at entry;
     0x84fa4 `beq 0x7d, c`   the MODEL branch, decided by the condition the stage adds.
   MEMBER ARM (c <> 125): the run reaches grow's entry A_grow with a0 = v, ra = 0x84fb0, sp unchanged; the segment
   WRITES NOTHING (it only loads). No __asan_report_* and no UBSan trap is reached.
   THE CURSOR BYTE is the env atom xatom 20, never a Rocq variable: a variable inside the symbolic state leaves the
   engine's `beq 0x7d, c` unreduced (MEASURED: the vm_compute of the run then does not terminate). *)
Section WB. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.

Lemma pi_stageB_member : forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs0 regsR memR mdR
  (STK ot sp0 : Z) (FP : list (Z * Z)) kj q v p e d kids keys n cap c
  (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ pi_xsR p e d regs0 kids keys n cap c)) pi_ssB0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) ->
  @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR kj ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 144 -> sp0 <= ot -> ot - STK <= sp0 - 144 ->
  YK11.getr regsR 8 = w64 (q + 16) -> YK11.getr regsR 9 = w64 q -> YK11.getr regsR 18 = w64 1 ->
  YK11.getr regsR 19 = w64 v -> YK11.getr regsR 25 = w64 (pi_sh (q + 16)) ->
  YK11.getr regsR 26 = w64 SHADOW_OFF -> YK11.getr regsR 27 = w64 (pi_sh q) ->
  2 ^ 46 <= q -> sp0 <= q -> q + 24 <= ot -> q + 24 <= 2 ^ 47 ->
  4096 <= v -> v + 56 <= alloc_ceiling ->
  4096 <= p -> p + 1 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e <= 2 ^ 47 - 2 ^ 23 -> 1 <= d <= 2 ->
  0 <= kids < 2 ^ 64 -> 0 <= keys < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  p < e -> 0 <= c <= 255 -> c <> 125 ->
  val_mem tfibsegs (mrestrict (w_H W) memR) p 1 c ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF q 24 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF v 56 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF p 1 ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (forall a, p <= a < p + 1 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (v + 56 <= 0x10000 \/ FS_IMG_END <= v) -> (p + 1 <= 0x10000 \/ FS_IMG_END <= p) ->
  (v + 56 <= sp0 - 144 \/ ot <= v) -> (p + 1 <= sp0 - 144 \/ ot <= p) -> (p + 1 <= q \/ q + 24 <= p) ->
  (p + 1 <= v \/ v + 56 <= p) ->
  (forall a, v <= a < v + 56 ->
     awr_byte tfibsegs B STK ot FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall regsC memC mat,
     YK11.getr regsC 1 = w64 0x84fb0 -> spZ regsC = sp0 - 144 -> YK11.getr regsC 10 = w64 v ->
     YK11.getr regsC 8 = w64 (q + 16) -> YK11.getr regsC 9 = w64 q -> YK11.getr regsC 18 = w64 1 ->
     YK11.getr regsC 19 = w64 v -> YK11.getr regsC 20 = w64 (q + 8) ->
     YK11.getr regsC 23 = w64 (pi_sh (q + 8)) -> YK11.getr regsC 25 = w64 (pi_sh (q + 16)) ->
     YK11.getr regsC 26 = w64 SHADOW_OFF -> YK11.getr regsC 27 = w64 (pi_sh q) ->
     Forall (fun r => YK11.getr regsC r = YK11.getr regsR r) [3; 4; 21; 22; 24]%bv ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - 144 <= x < sp0) -> ~ (q <= x < q + 24) -> ~ (v <= x < v + 56) ->
        memC (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     mem_grows (mrestrict (w_H W) memR) (mrestrict (w_H W) memC) ->
     @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memC)
       (with_vm_backing (m_vm_lazy mdR) mat mdR) kj ->
     ARU tfibsegs B lyc Sc Uc W memC (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_grow regsC memC (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs)) mdR) Q.
Proof.
intros ly S W0 mem0 md0 own lyc Sc Uc W regs0 regsR memR mdR STK ot sp0 FP kj q v p e d kids keys n cap c Q
  HS HJ HARU Hsp Hsot Hlo R8 R9 R18 R19 R25 R26 R27
  Hq46 Hqsp Hqot Hq47 Hv1 Hv2 Hp1 Hp2 He Hd Hki Hky Hn Hcap Hpe Hc Hc125 HBV HRAq HRAv HRAp Happv Happp
  Himgv Himgp Hvsp Hpsp Hpq Hpv HWO KC.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
set (E := Ereg regsR (fs_extraT ++ pi_xsR p e d regs0 kids keys n cap c)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r)
  by (intros r; subst E; apply ew_Ereg_reg).
assert (EX : forall j, ew E (xatom j) = nth j (pi_xsR p e d regs0 kids keys n cap c) (Z_to_bv 64 0))
  by (intros j; subst E; apply fsw_ew_xatom).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (ER 2%bv); exact Hsp).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (ER 9%bv); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite (ER 19%bv); exact R19).
destruct (pi_xsR_nth p e d regs0 kids keys n cap c) as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20).
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (rewrite EX; exact X0).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 e) by (rewrite EX; exact X1).
assert (EX20 : ew E (xatom 20) = Z_to_bv 64 c) by (rewrite EX; exact X20).
(* ---- the cursor byte's atom fact ---- *)
assert (AFC : afact_ok E (xatom 20) (mkAF 0 255 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EX20, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_add_fact tfibsegs _ _ _ (xatom 20) (mkAF 0 255 0) HS AFC) as HSc. clear HS.
(* ---- the five re-seats: s0 = q + 16, s2 = 1, s9 = shadow (q + 16), s10 = SHADOW_OFF, s11 = shadow q ---- *)
assert (D8 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 8%bv
  = sv_denot E (SOff 9 16)).
{ cbn [ms_regs mkst]. rewrite R8. symmetry. apply bv_eq.
  change (bv_unsigned (sv_denot E (SOff 9 16))) with (YP0e.U E (SOff 9 16)).
  rewrite (U_atom_off E 9 q 16 E9 ltac:(lia) ltac:(lia)). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (D18 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 18%bv
  = sv_denot E (SLit 1)) by (cbn [ms_regs mkst]; rewrite R18; reflexivity).
assert (D25 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 25%bv
  = sv_denot E (pi_shx 9 16)).
{ cbn [ms_regs mkst]. rewrite R25. apply bv_eq. unfold w64.
  rewrite unsigned_lit_small by (unfold pi_sh, SHADOW_OFF; lia).
  change (bv_unsigned (sv_denot E (pi_shx 9 16))) with (YP0e.U E (pi_shx 9 16)).
  unfold pi_shx. symmetry. exact (pi_U_shadow E 9 16 q E9 ltac:(lia) ltac:(lia) ltac:(lia) E32). }
assert (D26 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 26%bv
  = sv_denot E (SOff 32 0)) by (cbn [ms_regs mkst]; rewrite R26, fsw_SOff0, E32; reflexivity).
assert (D27 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 27%bv
  = sv_denot E (pi_shx 9 0)).
{ cbn [ms_regs mkst]. rewrite R27. apply bv_eq. unfold w64.
  rewrite unsigned_lit_small by (unfold pi_sh, SHADOW_OFF; lia).
  change (bv_unsigned (sv_denot E (pi_shx 9 0))) with (YP0e.U E (pi_shx 9 0)).
  unfold pi_shx. rewrite (pi_U_shadow E 9 0 q E9 ltac:(lia) ltac:(lia) ltac:(lia) E32), Z.add_0_r. reflexivity. }
apply (st_ok_set_reg tfibsegs E _ _ 8%bv (SOff 9 16)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D8].
apply (st_ok_set_reg tfibsegs E _ _ 18%bv (SLit 1)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D18].
apply (st_ok_set_reg tfibsegs E _ _ 25%bv (pi_shx 9 16)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D25].
apply (st_ok_set_reg tfibsegs E _ _ 26%bv (SOff 32 0)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D26].
apply (st_ok_set_reg tfibsegs E _ _ 27%bv (pi_shx 9 0)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D27].
(* ---- the cursor byte as a region, and in->p < in->end ---- *)
assert (RB : region_ok tfibsegs E (mrestrict (w_H W) memR) pi_byte).
{ unfold region_ok, pi_byte.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EX0, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ p 0 1 (SOff (xatom 20) 0) c);
    [rewrite fsw_SOff0; exact EX20 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact HBV. }
assert (DJ : all_disjoint E pi_byte (ss_mem pi_ssB0)).
{ apply all_disjoint_of_extents.
  unfold pi_ssB0, fss_retT, fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pi_qR, pi_vR, pi_byte,
    extent_of_region.
  cbn [ss_mem app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EX0, E2, E9, E19, !unsigned_lit_small by lia.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END
    in Himgp |- *.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
apply (st_ok_add_region' tfibsegs E _ _ pi_byte) in HSc;
  [| vm_compute; reflexivity | cbn [ms_mem restrict]; exact RB | cbn [ss_mem]; exact DJ].
assert (CC1 : branch_taken BC_LTU (sv_denot E (SOff (xatom 0) 0)) (sv_denot E (SOff (xatom 1) 0)) = true).
{ rewrite branch_ltu_U, (U_atom E (xatom 0) p EX0 ltac:(lia)), (U_atom E (xatom 1) e EX1 ltac:(lia)).
  apply Z.ltb_lt. lia. }
apply (st_ok_add_cond tfibsegs E _ _ BC_LTU (SOff (xatom 0) 0) (SOff (xatom 1) 0)) in HSc; [| exact CC1].
(* ---- the brace test: the byte is not `}` ---- *)
assert (CC2 : branch_taken BC_EQ (sv_denot E (SLit 125)) (sv_denot E (SOff (xatom 20) 0)) = false).
{ rewrite branch_eq_U, U_lit by lia. rewrite (U_atom E (xatom 20) c EX20 ltac:(lia)).
  apply Z.eqb_neq. lia. }
apply (st_ok_add_cond_neg tfibsegs E _ _ BC_EQ (SLit 125) (SOff (xatom 20) 0)) in HSc; [| exact CC2].
(* ---- the three shadow entries ---- *)
assert (UB : YP0e.U E fs_Bx = SHADOW_OFF)
  by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok tfibsegs fs_Bx pi_SHR E (mrestrict (w_H W) memR)).
{ unfold sh_ok, pi_SHR. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx 9 q 24 q 0 24 HRAq UB
      ltac:(apply U_atom; [exact E9 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx 19 v 56 v 0 56 HRAv UB
      ltac:(apply U_atom; [exact E19 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. apply Happv. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx (xatom 0) p 1 p 0 1 HRAp UB
      ltac:(apply U_atom; [exact EX0 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. apply Happp. lia. }
change memR with (ms_mem (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) in HJ, HARU, SHOK.
(* ---- 0x84f5c .. 0x84fac: the shadow checks, the end test, the cursor byte, jal grow ---- *)
fsw_aj_run_to_tokU pitems_tbl_ok HSc HJ HARU SHOK fs_Bspan A_grow.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ee ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ee rs' a1 a2 a3 a4 a5 a6 a7 a8) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := sp0 - 144 - ot);
    [reflexivity | rewrite E2; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := q - ot);
    [reflexivity | rewrite E9, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_gen with (k := 19%nat) (b := v);
    [reflexivity | rewrite E19; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HWO. lia. }
assert (FR : forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - 144 <= x < sp0) -> ~ (q <= x < q + 24) -> ~ (v <= x < v + 56) ->
  ms_mem ms (Z_to_bv 64 x) = memR (Z_to_bv 64 x)).
{ intros x Hx H1 H2 H3. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?(unsigned_lit_small x) in Hr by lia;
    first [ lia | rewrite E2 in Hr; lia
          | rewrite E9, unsigned_lit_small in Hr by lia; lia
          | rewrite E19, unsigned_lit_small in Hr by lia; lia
          | rewrite EX0, unsigned_lit_small in Hr by lia; lia ] |]); destruct Hin. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HSc eq_refl).
lazymatch type of HSc with st_ok _ ?Ee _ _ => set (E' := Ee) in * end.
assert (EE : forall j, (j < 54)%nat -> ew E' j = ew E j)
  by (intros j Hj; unfold E'; rewrite !ew_ewset_other by lia; reflexivity).
assert (ER' : forall r : bv 5, ew E' (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r)
  by (intros r; pose proof (u5_range r); rewrite EE by lia; exact (ER r)).
assert (E2' : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite EE by lia; exact E2).
assert (E9' : ew E' 9 = Z_to_bv 64 q) by (rewrite EE by lia; exact E9).
assert (E19' : ew E' 19 = Z_to_bv 64 v) by (rewrite EE by lia; exact E19).
assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EE by lia; exact E32).
apply (KC (ms_regs ms) (ms_mem ms) mat);
  [ | | | | | | | | | | | | | exact FR | exact HG | exact HJ | exact HARU].
- pi_gw_reg HSc (1%bv : bv 5). pi_gw_val. apply U_lit. lia.
- unfold spZ at 1.
  rewrite (fsw_reg_off _ _ _ ms 2%bv 2 0 (sp0 - 144) HSc ltac:(vm_compute; reflexivity) E2' ltac:(lia)). lia.
- pi_gw_reg HSc (10%bv : bv 5). pi_gw_val. apply U_atom; [exact E19' | lia].
- pi_gw_reg HSc (8%bv : bv 5). pi_gw_val. apply U_atom_off; [exact E9' | lia | lia].
- pi_gw_reg HSc (9%bv : bv 5). pi_gw_val. apply U_atom; [exact E9' | lia].
- pi_gw_reg HSc (18%bv : bv 5). pi_gw_val. apply U_lit. lia.
- pi_gw_reg HSc (19%bv : bv 5). pi_gw_val. apply U_atom; [exact E19' | lia].
- pi_gw_reg HSc (20%bv : bv 5). pi_gw_val. apply U_atom_off; [exact E9' | lia | lia].
- pi_gw_reg HSc (23%bv : bv 5). pi_gw_val.
  exact (pi_U_shadow E' 9 8 q E9' ltac:(lia) ltac:(lia) ltac:(lia) E32').
- pi_gw_reg HSc (25%bv : bv 5). pi_gw_val.
  exact (pi_U_shadow E' 9 16 q E9' ltac:(lia) ltac:(lia) ltac:(lia) E32').
- pi_gw_reg HSc (26%bv : bv 5). pi_gw_val. apply U_atom; [exact E32' | unfold SHADOW_OFF; lia].
- pi_gw_reg HSc (27%bv : bv 5). pi_gw_val.
  rewrite (pi_U_shadow E' 9 0 q E9' ltac:(lia) ltac:(lia) ltac:(lia) E32'), Z.add_0_r. reflexivity.
- repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ =>
    pi_gw_reg HSc r; rewrite fsw_SOff0; exact (ER' r) end|]). apply Forall_nil.
Qed.
End WB.

(* the callee-saved registers at parse_items' `ret`: sp back up by the frame, and the thirteen the epilogue reloads
   from the frame (the entry values, xatom 3 .. 15 in pi_saved_regs order) *)
Definition pi_expect_close (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 144
  | 8 => SOff (xatom 4) 0 | 9 => SOff (xatom 5) 0 | 18 => SOff (xatom 6) 0 | 19 => SOff (xatom 7) 0
  | 20 => SOff (xatom 8) 0 | 21 => SOff (xatom 9) 0 | 22 => SOff (xatom 10) 0 | 23 => SOff (xatom 11) 0
  | 24 => SOff (xatom 12) 0 | 25 => SOff (xatom 13) 0 | 26 => SOff (xatom 14) 0 | 27 => SOff (xatom 15) 0
  | z => SOff (Z.to_nat z) 0
  end.

Section WC. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.

(* ---- STAGE B, CLOSE ARM (the byte is `}`: the EMPTY object): 0x84f5c .. the `ret` 0x852fc ---- *)
Lemma pi_stageB_close : forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs0 regsR memR mdR
  (STK ot sp0 : Z) (FP : list (Z * Z)) kj q v p e d kids keys n cap
  (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ pi_xsR p e d regs0 kids keys n cap 125)) pi_ssB0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) ->
  @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR kj ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 144 -> sp0 = spZ regs0 -> sp0 <= ot -> ot - STK <= sp0 - 144 ->
  YK11.getr regsR 3 = YK11.getr regs0 3 -> YK11.getr regsR 4 = YK11.getr regs0 4 ->
  YK11.getr regsR 8 = w64 (q + 16) -> YK11.getr regsR 9 = w64 q -> YK11.getr regsR 18 = w64 1 ->
  YK11.getr regsR 19 = w64 v -> YK11.getr regsR 25 = w64 (pi_sh (q + 16)) ->
  YK11.getr regsR 26 = w64 SHADOW_OFF -> YK11.getr regsR 27 = w64 (pi_sh q) ->
  2 ^ 46 <= q -> sp0 <= q -> q + 24 <= ot -> q + 24 <= 2 ^ 47 ->
  4096 <= v -> v + 56 <= alloc_ceiling ->
  4096 <= p -> p + 1 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e <= 2 ^ 47 - 2 ^ 23 -> 1 <= d <= 2 ->
  0 <= kids < 2 ^ 64 -> 0 <= keys < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  p < e ->
  val_mem tfibsegs (mrestrict (w_H W) memR) p 1 125 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF q 24 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF v 56 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF p 1 ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (forall a, p <= a < p + 1 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (v + 56 <= 0x10000 \/ FS_IMG_END <= v) -> (p + 1 <= 0x10000 \/ FS_IMG_END <= p) ->
  (v + 56 <= sp0 - 144 \/ ot <= v) -> (p + 1 <= sp0 - 144 \/ ot <= p) -> (p + 1 <= q \/ q + 24 <= p) ->
  (p + 1 <= v \/ v + 56 <= p) ->
  (forall a, v <= a < v + 56 ->
     awr_byte tfibsegs B STK ot FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall Ef ssf msf mat,
     st_ok tfibsegs Ef ssf (restrict (w_H W) msf) -> ss_resv ssf = None ->
     clookup pitems_tbl (ss_pc ssf) = Some RET_WORD_r ->
     YK11.getr (ms_regs msf) 1 = YK11.getr regs0 1 -> YK11.getr (ms_regs msf) 10 = w64 0 ->
     aregs_preserved regs0 (ms_regs msf) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) q 8 (p + 1) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 8) 8 e ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 16) 4 (d - 1) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) v 4 6 ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 8) 8 0 ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 16) 8 0 ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 24) 8 kids ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 32) 8 keys ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 40) 8 n ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 48) 8 cap ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - 144 <= x < sp0) -> ~ (q <= x < q + 24) -> ~ (v <= x < v + 56) ->
        ms_mem msf (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     mem_grows (mrestrict (w_H W) memR) (mrestrict (w_H W) (ms_mem msf)) ->
     @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc (ms_mem msf))
       (with_vm_backing (m_vm_lazy mdR) mat mdR) kj ->
     ARU tfibsegs B lyc Sc Uc W (ms_mem msf) (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (mkCfg msf (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs)) mdR) Q.
Proof.
intros ly S W0 mem0 md0 own lyc Sc Uc W regs0 regsR memR mdR STK ot sp0 FP kj q v p e d kids keys n cap Q
  HS HJ HARU Hsp Hsp0 Hsot Hlo R3 R4 R8 R9 R18 R19 R25 R26 R27
  Hq46 Hqsp Hqot Hq47 Hv1 Hv2 Hp1 Hp2 He Hd Hki Hky Hn Hcap Hpe HBV HRAq HRAv HRAp Happv Happp
  Himgv Himgp Hvsp Hpsp Hpq Hpv HWO KRET.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
set (E := Ereg regsR (fs_extraT ++ pi_xsR p e d regs0 kids keys n cap 125)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r)
  by (intros r; subst E; apply ew_Ereg_reg).
assert (EX : forall j, ew E (xatom j) = nth j (pi_xsR p e d regs0 kids keys n cap 125) (Z_to_bv 64 0))
  by (intros j; subst E; apply fsw_ew_xatom).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (ER 2%bv); exact Hsp).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (ER 9%bv); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite (ER 19%bv); exact R19).
destruct (pi_xsR_nth p e d regs0 kids keys n cap 125) as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20).
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (rewrite EX; exact X0).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 e) by (rewrite EX; exact X1).
assert (EX2 : ew E (xatom 2) = Z_to_bv 64 d) by (rewrite EX; exact X2).
assert (EX20 : ew E (xatom 20) = Z_to_bv 64 125) by (rewrite EX; exact X20).
assert (EX16 : ew E (xatom 16) = Z_to_bv 64 kids) by (rewrite EX; exact X16).
assert (EX17 : ew E (xatom 17) = Z_to_bv 64 keys) by (rewrite EX; exact X17).
assert (EX18 : ew E (xatom 18) = Z_to_bv 64 n) by (rewrite EX; exact X18).
assert (EX19 : ew E (xatom 19) = Z_to_bv 64 cap) by (rewrite EX; exact X19).
assert (AFC : afact_ok E (xatom 20) (mkAF 0 255 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EX20, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_add_fact tfibsegs _ _ _ (xatom 20) (mkAF 0 255 0) HS AFC) as HSc. clear HS.
assert (D8 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 8%bv
  = sv_denot E (SOff 9 16)).
{ cbn [ms_regs mkst]. rewrite R8. symmetry. apply bv_eq.
  change (bv_unsigned (sv_denot E (SOff 9 16))) with (YP0e.U E (SOff 9 16)).
  rewrite (U_atom_off E 9 q 16 E9 ltac:(lia) ltac:(lia)). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (D18 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 18%bv
  = sv_denot E (SLit 1)) by (cbn [ms_regs mkst]; rewrite R18; reflexivity).
assert (D25 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 25%bv
  = sv_denot E (pi_shx 9 16)).
{ cbn [ms_regs mkst]. rewrite R25. apply bv_eq. unfold w64.
  rewrite unsigned_lit_small by (unfold pi_sh, SHADOW_OFF; lia).
  change (bv_unsigned (sv_denot E (pi_shx 9 16))) with (YP0e.U E (pi_shx 9 16)).
  unfold pi_shx. symmetry. exact (pi_U_shadow E 9 16 q E9 ltac:(lia) ltac:(lia) ltac:(lia) E32). }
assert (D26 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 26%bv
  = sv_denot E (SOff 32 0)) by (cbn [ms_regs mkst]; rewrite R26, fsw_SOff0, E32; reflexivity).
assert (D27 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 27%bv
  = sv_denot E (pi_shx 9 0)).
{ cbn [ms_regs mkst]. rewrite R27. apply bv_eq. unfold w64.
  rewrite unsigned_lit_small by (unfold pi_sh, SHADOW_OFF; lia).
  change (bv_unsigned (sv_denot E (pi_shx 9 0))) with (YP0e.U E (pi_shx 9 0)).
  unfold pi_shx. rewrite (pi_U_shadow E 9 0 q E9 ltac:(lia) ltac:(lia) ltac:(lia) E32), Z.add_0_r. reflexivity. }
apply (st_ok_set_reg tfibsegs E _ _ 8%bv (SOff 9 16)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D8].
apply (st_ok_set_reg tfibsegs E _ _ 18%bv (SLit 1)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D18].
apply (st_ok_set_reg tfibsegs E _ _ 25%bv (pi_shx 9 16)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D25].
apply (st_ok_set_reg tfibsegs E _ _ 26%bv (SOff 32 0)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D26].
apply (st_ok_set_reg tfibsegs E _ _ 27%bv (pi_shx 9 0)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D27].
assert (RB : region_ok tfibsegs E (mrestrict (w_H W) memR) pi_byte).
{ unfold region_ok, pi_byte.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EX0, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ p 0 1 (SOff (xatom 20) 0) 125);
    [rewrite fsw_SOff0; exact EX20 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact HBV. }
assert (DJ : all_disjoint E pi_byte (ss_mem pi_ssB0)).
{ apply all_disjoint_of_extents.
  unfold pi_ssB0, fss_retT, fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pi_qR, pi_vR, pi_byte,
    extent_of_region.
  cbn [ss_mem app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EX0, E2, E9, E19, !unsigned_lit_small by lia.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END
    in Himgp |- *.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
apply (st_ok_add_region' tfibsegs E _ _ pi_byte) in HSc;
  [| vm_compute; reflexivity | cbn [ms_mem restrict]; exact RB | cbn [ss_mem]; exact DJ].
assert (CC1 : branch_taken BC_LTU (sv_denot E (SOff (xatom 0) 0)) (sv_denot E (SOff (xatom 1) 0)) = true).
{ rewrite branch_ltu_U, (U_atom E (xatom 0) p EX0 ltac:(lia)), (U_atom E (xatom 1) e EX1 ltac:(lia)).
  apply Z.ltb_lt. lia. }
apply (st_ok_add_cond tfibsegs E _ _ BC_LTU (SOff (xatom 0) 0) (SOff (xatom 1) 0)) in HSc; [| exact CC1].
(* the brace test: the byte IS `}` *)
assert (CC2 : branch_taken BC_EQ (sv_denot E (SLit 125)) (sv_denot E (SOff (xatom 20) 0)) = true).
{ rewrite branch_eq_U, U_lit by lia. rewrite (U_atom E (xatom 20) 125 EX20 ltac:(lia)).
  apply Z.eqb_eq. reflexivity. }
apply (st_ok_add_cond tfibsegs E _ _ BC_EQ (SLit 125) (SOff (xatom 20) 0)) in HSc; [| exact CC2].
assert (UB : YP0e.U E fs_Bx = SHADOW_OFF)
  by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok tfibsegs fs_Bx pi_SHR E (mrestrict (w_H W) memR)).
{ unfold sh_ok, pi_SHR. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx 9 q 24 q 0 24 HRAq UB
      ltac:(apply U_atom; [exact E9 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx 19 v 56 v 0 56 HRAv UB
      ltac:(apply U_atom; [exact E19 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. apply Happv. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx (xatom 0) p 1 p 0 1 HRAp UB
      ltac:(apply U_atom; [exact EX0 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. apply Happp. lia. }
change memR with (ms_mem (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) in HJ, HARU, SHOK.
(* ---- 0x84f5c .. the ret 0x852fc: the close, the depth check, the epilogue ---- *)
fsw_aj_run_tokU pitems_tbl_ok HSc HJ HARU SHOK fs_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ee ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ee rs' a1 a2 a3 a4 a5 a6 a7 a8) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := sp0 - 144 - ot);
    [reflexivity | rewrite E2; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := q - ot);
    [reflexivity | rewrite E9, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_gen with (k := 19%nat) (b := v);
    [reflexivity | rewrite E19; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HWO. lia. }
assert (FR : forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - 144 <= x < sp0) -> ~ (q <= x < q + 24) -> ~ (v <= x < v + 56) ->
  ms_mem ms (Z_to_bv 64 x) = memR (Z_to_bv 64 x)).
{ intros x Hx H1 H2 H3. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?(unsigned_lit_small x) in Hr by lia;
    first [ lia | rewrite E2 in Hr; lia
          | rewrite E9, unsigned_lit_small in Hr by lia; lia
          | rewrite E19, unsigned_lit_small in Hr by lia; lia
          | rewrite EX0, unsigned_lit_small in Hr by lia; lia ] |]); destruct Hin. }
lazymatch type of HSc with st_ok _ ?Ee _ _ => set (E' := Ee) in * end.
assert (EE : forall j, (j < 54)%nat -> ew E' j = ew E j)
  by (intros j Hj; unfold E'; rewrite !ew_ewset_other by lia; reflexivity).
assert (E2' : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite EE by lia; exact E2).
assert (E9' : bv_unsigned (ew E' 9) = q)
  by (rewrite EE by lia; rewrite E9; apply unsigned_lit_small; lia).
assert (E19' : bv_unsigned (ew E' 19) = v)
  by (rewrite EE by lia; rewrite E19; apply unsigned_lit_small; lia).
pose proof (fsw_region_nth _ _ _ 4 _ HSc eq_refl) as HRQ.
pose proof (fsw_region_nth _ _ _ 5 _ HSc eq_refl) as HRV.
cbn [ms_mem restrict] in HRQ, HRV.
assert (DX : forall j z, ew E (xatom j) = Z_to_bv 64 z -> (j <= 20)%nat -> 0 <= z < 2 ^ 64 ->
  sv_denot E' (SOff (xatom j) 0) = Z_to_bv 64 z)
  by (intros j z Hj Hj20 Hz; rewrite fsw_SOff0, EE by (unfold xatom; lia); exact Hj).
assert (XX : forall j, (j < 13)%nat ->
  sv_denot E' (SOff (xatom (3 + j)) 0) = YK11.getr regs0 (nth j pi_saved_regs 0%bv)).
{ intros j Hj. rewrite fsw_SOff0, EE by (unfold xatom; lia).
  exact (eq_trans (EX (3 + j)%nat) (XR j Hj)). }
apply (KRET E' _ ms mat HSc eq_refl ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ (1%bv : bv 5) HSc).
  lazymatch goal with |- sv_denot _ (sr_get ?l ?r) = _ =>
    let x := eval vm_compute in (sr_get l r) in change (sr_get l r) with x end.
  exact (XX 0%nat ltac:(lia)).
- pi_gw_reg HSc (10%bv : bv 5). pi_gw_val. apply U_lit. lia.
- apply (fsw_preserved (w_H W) E' _ ms regs0 pi_expect_close HSc ltac:(vm_compute; reflexivity)).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (pi_expect_close ?x) = _ =>
    let y := eval vm_compute in (pi_expect_close x) in change (pi_expect_close x) with y end.
  + apply bv_eq. rewrite denot_SOff, E2', Hsp0. unfold spZ.
    replace (bv_unsigned (YK11.getr regs0 2) - 144 + 144) with (bv_unsigned (YK11.getr regs0 2)) by lia.
    apply zcanon_id. unfold M64. apply u64_range.
  + rewrite fsw_SOff0, EE by lia. rewrite (ER 3%bv). exact R3.
  + rewrite fsw_SOff0, EE by lia. rewrite (ER 4%bv). exact R4.
  + exact (XX 1%nat ltac:(lia)).
  + exact (XX 2%nat ltac:(lia)).
  + exact (XX 3%nat ltac:(lia)).
  + exact (XX 4%nat ltac:(lia)).
  + exact (XX 5%nat ltac:(lia)).
  + exact (XX 6%nat ltac:(lia)).
  + exact (XX 7%nat ltac:(lia)).
  + exact (XX 8%nat ltac:(lia)).
  + exact (XX 9%nat ltac:(lia)).
  + exact (XX 10%nat ltac:(lia)).
  + exact (XX 11%nat ltac:(lia)).
  + exact (XX 12%nat ltac:(lia)).
- replace q with (q + 0) at 1 by lia.
  apply (fsw_field _ _ 9 _ _ _ _ _ _ 0 8%N (SOff (xatom 0) 1) (p + 1) HRQ E9' ltac:(cbn; tauto));
    [| cbn; lia | cbn; lia].
  apply bv_eq. rewrite denot_SOff, EE by (unfold xatom; lia). rewrite EX0, unsigned_lit_small by lia.
  rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
- apply (fsw_field _ _ 9 _ _ _ _ _ _ 8 8%N (SOff (xatom 1) 0) e HRQ E9' ltac:(cbn; tauto));
    [exact (DX 1%nat e EX1 ltac:(lia) ltac:(lia)) | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 9 _ _ _ _ _ _ 16 4%N (SOff (xatom 2) (-1)) (d - 1) HRQ E9' ltac:(cbn; tauto));
    [| cbn; lia | cbn; lia].
  apply bv_eq. rewrite denot_SOff, EE by (unfold xatom; lia). rewrite EX2, unsigned_lit_small by lia.
  rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
- replace v with (v + 0) at 1 by lia.
  apply (fsw_field _ _ 19 _ _ _ _ _ _ 0 4%N (SLit 6) 6 HRV E19' ltac:(cbn; tauto)); [reflexivity | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 19 _ _ _ _ _ _ 8 8%N (SLit 0) 0 HRV E19' ltac:(cbn; tauto)); [reflexivity | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 19 _ _ _ _ _ _ 16 8%N (SLit 0) 0 HRV E19' ltac:(cbn; tauto)); [reflexivity | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 19 _ _ _ _ _ _ 24 8%N (SOff (xatom 16) 0) kids HRV E19' ltac:(cbn; tauto));
    [exact (DX 16%nat kids EX16 ltac:(lia) ltac:(lia)) | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 19 _ _ _ _ _ _ 32 8%N (SOff (xatom 17) 0) keys HRV E19' ltac:(cbn; tauto));
    [exact (DX 17%nat keys EX17 ltac:(lia) ltac:(lia)) | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 19 _ _ _ _ _ _ 40 8%N (SOff (xatom 18) 0) n HRV E19' ltac:(cbn; tauto));
    [exact (DX 18%nat n EX18 ltac:(lia) ltac:(lia)) | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 19 _ _ _ _ _ _ 48 8%N (SOff (xatom 19) 0) cap HRV E19' ltac:(cbn; tauto));
    [exact (DX 19%nat cap EX19 ltac:(lia) ltac:(lia)) | cbn; lia | cbn; lia].
- exact FR.
- exact HG.
- exact HJ.
- exact HARU.
Qed.
End WC.
