(* rule 24: proves no function (kind: helper lemmas of check_round_trip's D1 segment lemma, PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd16.v crt16_runB :541 - the bespoke ASan proof of THIS function on THESE fs.asan bytes). CHECKER VERDICT: CONFIRM (a Theorem Labs lane, role check, 2026-10-29 04:3xZ) on (internal path), whose lines 6-21 carry the full reuse search (proof index v5 built 2026-10-29T01:50:18Z: `proof-index check_round_trip` 31 named hits, all plain/ubsan 0x138ac/0x139ac, none ASan; `proof-index check_round_trip_holds` empty; `proof-index 0x81a9c` / `0x81b9c` empty; control `proof-index 0x138ac` = 0 with 40 fs files by git grep; the exact hit's Require closure is 334 files with 0 Admitted/Axiom/Parameter).

   check_round_trip (fs.asan 0x81a9c), build A, lane D1, segment 31: the data premises of FSH_crt_base.crt_bcmp_call
   about the two byte ranges of `bcmp (got, bd, len)`, at a state of the walk. The donor's crt16_runB takes them as its
   own premises (bytes_at d2 bsb, bytes_at b bsb, addressable, end_in_app, the stack-window disjunctions); here they are
   produced in the S0 forms:
   - got = p, the second decode's block: its facts are the current state's (fs_rblock and zbytes_at at p);
   - bd, the caller's body block: crt_base gives its block and its bytes at the ENTRY memory; the block is live now (the
     boundary invariant's keep, Hkeep) and ajournal's block clause carries each byte to the current memory (no byte of
     a block is an image byte, YCbq.blk_img, and FS_PSTAT_FP holds image bytes only, FSH_crt_base.crt_pstat_img).
   The shadow facts come from AR at the CURRENT state: al_shadow's hull and, on the raw memory, the body of a live block
   is addressable when U holds only block heads (FSupoisonU.fs_heads, FSW_rd.fsw_block_body_addressable). That is the
   one premise beyond the requested statement: without it a range of U3 may lie inside a block body (upoison_ok allows
   it) and its raw shadow byte then reads 0xf7, so range_addressable fails. Every crt_INV_* of FSH_crt_base carries
   `FSupoisonU.fs_heads B ly3 S3 U3`.
   The byte list of the body is read back unchanged (zs (bz bs) = bs): the decode's zbytes_at at p makes every byte of
   bs lie in [0, 256) (YI00.garr8_bytes_ok); the donor's crt16_zb_map is the same fact.
   A new file: no licence lines (internal). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_K3 FSH_Fn_reader
FSH_Fn_writer FSH_Fn_crt FSW_frame FSW_frame3 FSW_rres FSW_crt_tbl FSW_strkit FSW_rd FSH_crt_base FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- pure facts ---- *)
Lemma crtD1_req_size : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); [lia | reflexivity]. Qed.

(* a list of byte values reads back unchanged through bz / zs (the donor's crt16_zb_map) *)
Lemma crtD1_zs_bz : forall l, Forall (fun b => 0 <= b < 256) l -> HState.zs (HState.bz l) = l.
Proof.
intros l Hl. unfold HState.zs, HState.bz. induction Hl as [|x l Hx Hl IH]; [reflexivity|].
cbn [map]. rewrite IH. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(* a byte window's view (YI00.garr8_mbyte read through aview) *)
Lemma crtD1_zb_view : forall (W : world tfibsegs) mem p l i, zbytes_at tfibsegs W mem p l ->
  0 <= i < Z.of_nat (length l) ->
  aview tfibsegs (w_H W) mem (p + i) = Some (bv_unsigned (Z_to_bv 8 (nth (Z.to_nat i) l 0))).
Proof.
intros W mem p l i H Hi. unfold aview.
replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
rewrite (garr8_mbyte tfibsegs (mrestrict (w_H W) mem) p l (Z.to_nat i) H ltac:(lia)). reflexivity.
Qed.

(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma crtD1_hull_sub : forall (rd : reader) P N x len, shadow_hull_vis rd P N -> P <= x -> 0 < len ->
  x + len <= P + N -> shadow_hull_vis rd x len.
Proof.
intros rd P N x len H H1 H2 H3 s Hs. apply H.
pose proof (Z.div_le_mono P x 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x + len - 1) (P + N - 1) 8 ltac:(lia) ltac:(lia)) as D2.
assert (A1 : shadow_addr P <= shadow_addr x) by (unfold shadow_addr; lia).
assert (A2 : shadow_addr (x + len - 1) <= shadow_addr (P + N - 1)) by (unfold shadow_addr; lia).
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) A1) as D3.
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) A2) as D4.
lia.
Qed.

(* a byte visible on the unpoisoned memory is visible on the raw one: a user-poisoned shadow byte reads 0xf7 *)
Lemma crtD1_vis_raw : forall U (W : world tfibsegs) mem s, upoisoned tfibsegs W mem U ->
  aview tfibsegs (w_H W) (unpoison U mem) s <> None -> aview tfibsegs (w_H W) mem s <> None.
Proof.
intros U W mem s HP Hv. destruct (in_ush U (bv_unsigned (Z_to_bv 64 s))) eqn:E.
- rewrite (aview_mod tfibsegs (w_H W) mem s).
  assert (Es : s mod 2 ^ 64 = bv_unsigned (Z_to_bv 64 s)).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. }
  rewrite Es, (HP _ E). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem s E). exact Hv.
Qed.

Section d1bd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- the user bytes [x, x + len) of a block live at a state: bounds, amem_range, no image byte, application bytes,
   and their shadow on the RAW memory (addressable, hull visible) ---- *)
Lemma crtD1_blk_user : forall ly S U (W : world tfibsegs) mem md P N x len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> In (P, N) (ablocks B ly S) ->
  P + HEAD <= x -> 0 <= len -> x + len <= P + req_size N ->
  4096 <= x /\ x + len <= alloc_ceiling /\ N < MALLOC_MAX /\ amem_range x len /\
  (forall a, x <= a < x + len -> ~ in_img tfibsegs a /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x len /\
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x len).
Proof.
intros ly S U W mem md P N x len HARU FH Hin Hx Hl Hn.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HARU as (_ & _ & HP).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P N HAR Hin)
  as (_ & H4096 & Hceil & Happ & _ & _ & HMx).
destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md P N HAR Hin) as (_ & Hhull).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
cbv [HEAD] in Hx.
cbv [in_app kLowShadowBeg] in Happ. rewrite C3 in Happ.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold amem_range. rewrite C3, C4, C5.
  destruct Happ as (_ & [Hlo | (Hh1 & _)]); [left; lia | right; split; lia]. }
split.
{ intros a Ha. split.
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md P N a HAR Hin ltac:(lia)).
  - cbv [SHADOW_OFF]. destruct Happ as (_ & [Hlo | (Hh1 & _)]); [left; lia | right; rewrite C3; lia]. }
split.
{ exact (fsw_block_body_addressable B ly S U W mem md P N x len HARU FH Hin ltac:(lia) Hl Hn). }
intros Hl0 s Hs. apply (crtD1_vis_raw U W mem s HP).
exact (crtD1_hull_sub _ P (req_size N) x len Hhull ltac:(lia) Hl0 Hn s Hs).
Qed.

(* ---- every premise crt_bcmp_call asks of the two ranges, at a state of the walk. `Hkeep` is what the lane's boundary
   invariant supplies (its Permutation of ablocks gives it): every block live at the entry is still live. `FH3` is the
   invariant's `FSupoisonU.fs_heads B ly3 S3 U3`: the raw shadow of a block body is addressable only when no range of
   U3 lies in it. ---- *)
Lemma crtD1_bcmp_data : forall cx ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT k p n,
  crt_base B cx ->
  @ajournal rc SK tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  (forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3)) ->
  fs_rblock tfibsegs B ly3 S3 W3 memT p n -> zbytes_at tfibsegs W3 memT p (c_bs cx) ->
  Z.of_nat (length (c_bs cx)) <= n ->
  spZ regsT = crt_sp1 cx ->
  let len := Z.of_nat (length (c_bs cx)) in
  0 <= len < 2 ^ 32 /\ 0 <= p /\ p + len <= 2 ^ 63 /\ 0 <= c_bd cx /\ c_bd cx + len <= 2 ^ 63 /\
  src_ok tfibsegs W3 regsT memT p len /\ src_ok tfibsegs W3 regsT memT (c_bd cx) len /\
  (forall a, p <= a < p + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  (forall a, c_bd cx <= a < c_bd cx + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  amem_range p len /\ amem_range (c_bd cx) len /\
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF p len /\
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) p len) /\
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF (c_bd cx) len /\
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) (c_bd cx) len) /\
  (forall i, 0 <= i < len -> aview tfibsegs (w_H W3) memT (c_bd cx + i) = aview tfibsegs (w_H W3) memT (p + i)).
Proof.
intros cx ly3 S3 U3 W3 regsT memT mdT k p n Hb HJ HARU3 FH3 Hkeep Hrb Hzp Hln Hsp. cbv zeta.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
destruct Hb as (Hpre & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hzbd & (k0 & Hrb0 & Hk0) & _).
destruct Hpre as (((HAR0 & _) & Hok0 & Hp0) & _).
assert (HARU0 : ARU tfibsegs B (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx))
  by (split; [exact HAR0 | split; [exact Hok0 | exact Hp0]]).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hsl & Hslo & _).
destruct (crt_sp1_facts cx Hal16 ltac:(lia)) as (Hsp1b & _ & _).
(* the two blocks at the current state *)
destruct Hrb as (Hin3p & _ & Hn0 & _).
destruct Hrb0 as (Hin0 & _ & Hk00 & _).
pose proof (Hkeep _ Hin0) as Hin3b.
assert (Rp : req_size (n + HEAD) = n + HEAD) by (apply crtD1_req_size; cbv [HEAD]; lia).
assert (Rb : req_size (k0 + HEAD) = k0 + HEAD) by (apply crtD1_req_size; cbv [HEAD]; lia).
destruct (crtD1_blk_user ly3 S3 U3 W3 memT mdT (p - HEAD) (n + HEAD) p (Z.of_nat (length (c_bs cx)))
  HARU3 FH3 Hin3p ltac:(lia) ltac:(lia) ltac:(rewrite Rp; lia))
  as (Hp4096 & Hpc & HpMx & Hpm & Hpi & Hpa & Hph).
destruct (crtD1_blk_user ly3 S3 U3 W3 memT mdT (c_bd cx - HEAD) (k0 + HEAD) (c_bd cx) (Z.of_nat (length (c_bs cx)))
  HARU3 FH3 Hin3b ltac:(lia) ltac:(lia) ltac:(rewrite Rb; lia))
  as (Hb4096 & Hbc & _ & Hbm & Hbi & Hba & Hbh).
cbv [MALLOC_MAX HEAD] in HpMx.
(* no byte below alloc_ceiling is in the callee's stack window: sp = sp1 >= sp0 - 208 >= alloc_ceiling + STK - 208 *)
assert (HW : forall a, a < alloc_ceiling -> a < spZ regsT - 2 * ESTACK).
{ intros a Ha. rewrite Hsp. unfold ESTACK. lia. }
(* the body's bytes: kept from the entry by the journal's block clause, read back through zs / bz *)
assert (Hok : Forall (fun b => 0 <= b < 256) (c_bs cx)) by exact (garr8_bytes_ok tfibsegs _ _ _ Hzp).
rewrite (crtD1_zs_bz _ Hok) in Hzbd.
assert (EQ : forall i, 0 <= i < Z.of_nat (length (c_bs cx)) ->
  aview tfibsegs (w_H W3) memT (c_bd cx + i) = aview tfibsegs (w_H W3) memT (p + i)).
{ intros i Hi.
  rewrite (crtD1_zb_view W3 memT p (c_bs cx) i Hzp Hi).
  rewrite <- (crtD1_zb_view (c_W cx) (c_mem cx) (c_bd cx) (c_bs cx) i Hzbd Hi).
  destruct (Hbi (c_bd cx + i) ltac:(lia)) as (Hni & Happ).
  apply (crt_raw_of_unp B (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) ly3 S3 U3 W3 memT mdT
    (c_bd cx + i) HARU0 HARU3); [change (2 ^ 64) with 18446744073709551616; lia | exact Happ|].
  pose proof (K2 (c_bd cx - HEAD) (k0 + HEAD) (HEAD + i) Hin0 Hin3b) as K.
  replace (c_bd cx - HEAD + (HEAD + i)) with (c_bd cx + i) in K by lia.
  apply K; [rewrite Rb; cbv [HEAD]; lia|].
  intros Hf. exact (Hni (crt_pstat_img _ Hf)). }
split; [change (2 ^ 32) with 4294967296; lia|].
split; [lia|].
split; [change (2 ^ 63) with 9223372036854775808; lia|].
split; [lia|].
split; [change (2 ^ 63) with 9223372036854775808; lia|].
split.
{ intros a Ha. split; [|pose proof (HW a ltac:(lia)); unfold ESTACK in *; lia].
  replace a with (p + (a - p)) by lia.
  rewrite (crtD1_zb_view W3 memT p (c_bs cx) (a - p) Hzp ltac:(lia)). discriminate. }
split.
{ intros a Ha. split; [|pose proof (HW a ltac:(lia)); unfold ESTACK in *; lia].
  replace a with (c_bd cx + (a - c_bd cx)) by lia.
  rewrite (EQ (a - c_bd cx) ltac:(lia)).
  rewrite (crtD1_zb_view W3 memT p (c_bs cx) (a - c_bd cx) Hzp ltac:(lia)). discriminate. }
split; [intros a Ha; pose proof (HW a ltac:(lia)); lia|].
split; [intros a Ha; pose proof (HW a ltac:(lia)); lia|].
split; [exact Hpm|].
split; [exact Hbm|].
split; [exact Hpa|].
split; [exact Hph|].
split; [exact Hba|].
split; [exact Hbh|].
exact EQ.
Qed.

End d1bd.

Print Assumptions crtD1_req_size.
Print Assumptions crtD1_zs_bz.
Print Assumptions crtD1_zb_view.
Print Assumptions crtD1_hull_sub.
Print Assumptions crtD1_vis_raw.
Print Assumptions crtD1_blk_user.
Print Assumptions crtD1_bcmp_data.
About crtD1_bcmp_data.
