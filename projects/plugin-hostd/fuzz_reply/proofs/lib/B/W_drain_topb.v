(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_dnrk.v, the memory bookkeeping that the image-B drain stages
   DROP / NEXT / REST and their shared memchr join (lib/B/W_drain_join.v, W_drain_next.v, W_drain_rest.v) need over
   lib/B/W_drain_cx.v's cut predicates.  Proves no function (kind: segment lemma).
   COPIED, with the prefix dtk_ renamed dnk_ and nothing else changed:
     dnk_low .. dnk_garr8_kept  from a working branch c0a3958f203
                                lib/B/W_drain_topb_bk.v:101-478 (the TOP tail lane's bookkeeping, itself ported from
                                lib/A/W_drain_epi.v; not yet on the drain base, so copied, not imported);
     dnk_nth_le_bytes, dnk_garr8_le, dnk_le_garr8, dnk_le8_bytes, dnk_le4_bytes, dnk_writable_view
                                from lib/B/W_gse_tail.v:65-185 (its gt_ lemmas), on the drain base.
   NEW here: dnk_entry_len, the entry field readers dnk_entry_skip / dnk_entry_buf / dnk_entry_used, and
   dnk_DMEM_call (DMEM survives a call whose writes all lie in its scratch below drain's frame: memchr's, at the
   memchr join 0x83990).
   ARx FORM (an internal work row): Section cx restates every lemma of Section c that reads AR over any allocator relation ARx
   (W_drain_cx_x.v's Section c header, plus HP0), with the suffix _x: the image-B twins of lib/A/W_drain_epi.v's
   Section cx (dend_*_x of DR_x slice B), where these lemmas came from; the journals are at W_contract_x.v's
   DRAIN_STK_x.  Section c is unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_drain_dnrk.v; 4397 of its 5046 lines of code are new or changed and 746 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_traps W_drain_cx W_drain_topb_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Definition dts_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition dts_gsh (c : Z) : cval := CVal 8 (SAlu ALU_SRL (SOff 8 c) (SLit 3)).
Definition dts_Bx1 : sv := SOff 19 0.
Definition dts_Bx2 : sv := SOff 32 0.
Definition dts_SHgs : list shent := [ mkSHE 8 0 96 ].
Definition dts_IMGF : afact := mkAF 0x10000 IMG_TOP 3.
Definition dts_HEAPF : afact := mkAF 4096 140737479966720 3.
Definition dts_PTRF : afact := mkAF 4096 140737479966720 0.

Definition dts_regs : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms
  24%bv (SOff 21 8)) 20%bv (SOff 21 16)) 22%bv (SOff 21 24)) 27%bv (SOff 21 32).

Definition dts_chunks : list YP09.chunk :=
[ YP09.mkChunk 40 (dts_gsh 8); YP09.mkChunk 48 (dts_gsh 56); YP09.mkChunk 56 (dts_gsh 48);
  YP09.mkChunk 64 (dts_gsh 40); YP09.mkChunk 72 (dts_gsh 32); YP09.mkChunk 80 (dts_gsh 16);
  YP09.mkChunk 104 (dts_gsh 24); YP09.mkChunk 152 (dts_gsh 12);
  YP09.mkChunk 240 (CVal 8 (SOff 32 0)) ].
Definition dts_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 352 0 0 dts_chunks.
Definition dts_framew : YP09.region := YP09.mkRegion (Some 2%nat) 0 352 16 200 dts_chunks.








Section c1.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Lemma dts_ulen_used : forall sg e1,
bzs (re_U e1) = drain_b_c.ds_u sg -> Z.of_nat (length (re_U e1)) = re_used e1 -> ulen sg = re_used e1.
Proof.
intros sg e1 Hu Hlen. unfold ulen. rewrite <- Hu. unfold bzs. rewrite length_map. exact Hlen.
Qed.

Lemma dts_room : forall ly1 S1 (W1 : world SEGS) m1 sg e1 h1,
DLINK sg e1 h1 -> aentry_okx B ly1 S1 W1 m1 e1 -> 4096 <= drain_b_c.ds_cap sg - ulen sg ->
ulen sg = re_used e1 /\ 4096 <= re_cap e1 - re_used e1 /\ 0 < re_cap e1.
Proof.
intros ly1 S1 W1 m1 sg e1 h1 HL HE Hroom.
pose proof HL as (Hcap & Hu & _).
destruct HE as (_ & _ & _ & _ & _ & _ & Hlen & Hle & _).
pose proof (dts_ulen_used sg e1 Hu Hlen) as Hul.
rewrite Hul in Hroom. rewrite <- Hcap in Hroom.
split; [exact Hul|]. split; [lia|]. lia.
Qed.

Lemma dts_buf_blk : forall ly1 S1 (W1 : world SEGS) m1 e1,
aentry_okx B ly1 S1 W1 m1 e1 -> 0 < re_cap e1 ->
In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\
Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1)).
Proof.
intros ly1 S1 W1 m1 e1 H Hcap.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
destruct Hb as [(Hc0 & _)|(_ & Hin & Hj & Hg)]; [lia|].
split; [exact Hin | split; [exact Hj | exact Hg]].
Qed.

Lemma dts_dinband_blk : forall ly1 S1 (W1 : world SEGS) m1 md1 p n,
AR SEGS B ly1 S1 W1 m1 md1 -> In (p, n) (ablocks B ly1 S1) -> 0 < n -> dinband p n.
Proof.
intros ly1 S1 W1 m1 md1 p n HAR Hin Hn.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 p n HAR Hin) as (H16 & H4096 & Hceil & _).
assert (Hrq : req_size n = n \/ n < req_size n).
{ unfold req_size. destruct (Z.eqb_spec n 0); [lia|]. lia. }
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
unfold dinband, DCEIL, ASAN_CEIL in *.
split; [lia|]. split; [lia|].
apply Z.mod_divide in H16; [|lia]. destruct H16 as (k & ->).
apply Z.mod_divide; [lia|]. exists (2 * k). lia.
Qed.

Lemma dts_pend_recs : forall sg e1 h1,
DLINK sg e1 h1 -> (drain_b_c.ds_pend sg = [] <-> hl_recs (hs_pending h1) = []).
Proof.
intros sg e1 h1 (_ & _ & _ & _ & _ & _ & Hp & _).
split; intros H.
- rewrite <- Hp in H. destruct (hl_recs (hs_pending h1)); [reflexivity | discriminate H].
- rewrite <- Hp, H. reflexivity.
Qed.

Lemma dts_dstrict : forall ly1 S1 (W1 : world SEGS) m1 sg e1 h1 HA,
asrc_at B ly1 S1 W1 m1 HA h1 -> DLINK sg e1 h1 -> dstrict sg.
Proof.
intros ly1 S1 W1 m1 sg e1 h1 HA HS HL.
pose proof HL as (_ & _ & _ & _ & _ & _ & Hp & Hoff & _).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhd & _).
intros r rs Hr.
rewrite <- Hp in Hr.
destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:Hrecs; [discriminate Hr|].
cbn [map] in Hr. injection Hr as Hr1 Hr2.
destruct Hhd as [(Hnil & _)|(r' & rs' & Hr' & Hlo & Hhi)]; [congruence|].
injection Hr' as <- <-.
rewrite <- Hoff, <- Hr1. unfold bzs. rewrite length_map. lia.
Qed.

Lemma dts_shent_gs : forall ly1 S1 (W1 : world SEGS) m1 md1 E (j : nat),
AR SEGS B ly1 S1 W1 m1 md1 -> (j < 4)%nat ->
U E dts_Bx1 = SHADOW_OFF + 12 * Z.of_nat j -> U E (SOff 8 0) = rg_s RG ->
sh_ok SEGS dts_Bx1 dts_SHgs E (mrestrict (w_H W1) m1).
Proof.
intros ly1 S1 W1 m1 md1 E j HAR Hj HB Hm.
pose proof HGSB as (G1 & G2 & G3).
unfold dts_SHgs, sh_ok. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
rewrite <- (aview_rd_of SEGS).
pose proof (azs_range_addressable B LAWS ly1 S1 W1 m1 md1 (rg_s RG) (4 * ASRC) HAR HGSZ) as HRA.
split.
- intros x Hx. rewrite Z.add_0_r in Hx.
  destruct (HRA (x + ASRC * Z.of_nat j) ltac:(unfold ASRC in *; lia)) as (s & Hs & Hok).
  exists s. split.
  + unfold shadow_of_addr in *.
    replace (SHADOW_OFF + 12 * Z.of_nat j + x / 8)
      with (SHADOW_OFF + (x + ASRC * Z.of_nat j) / 8); [exact Hs|].
    unfold ASRC. replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.div_add by lia. lia.
  + unfold saddr_ok in *. unfold ASRC in Hok.
    replace ((x + 96 * Z.of_nat j) mod 8) with (x mod 8) in Hok; [exact Hok|].
    replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.mod_add by lia. reflexivity.
- intros a Ha. unfold SHADOW_OFF, ASRC, IMG_TOP in *. lia.
Qed.


End c1.

Section c2.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Lemma dtm_feed_nil : forall r, feed r [] = r.
Proof. intros r. reflexivity. Qed.

Lemma dtm_lines_nil : forall r, lines r [] = [].
Proof. intros r. reflexivity. Qed.

Lemma dtm_pcapm_nil : forall n cap, pcapm n cap [] = cap.
Proof. intros n cap. reflexivity. Qed.

Lemma dtm_later_dclr : forall cx sg jb a tl,
  dwf sg -> 4096 <= drain_b_c.ds_cap sg - ulen sg -> drain_b_c.ds_eintr sg = true ->
  dlater cx sg jb a tl -> dlater cx (dclr sg) jb a tl.
Proof.
  intros cx sg jb a tl Hw Hg He (fuel & Hn & Hw1 & Ht & Hf).
  pose proof (dneed_dclr sg He) as Hd.
  destruct fuel as [|f]; [lia|].
  rewrite (drun_eintr f (dlive cx) (dxmx cx) sg jb a Hg He) in Ht, Hf.
  unfold dlater. exists f. split; [lia|]. split.
  - destruct Hw as (Hw0 & Hw2). split; [exact Hw0 | exact Hw2].
  - split; [exact Ht | exact Hf].
Qed.

Lemma dtm_pfut0 : forall cx sg jb a tl,
  dwf sg -> dstrict sg -> 4096 <= drain_b_c.ds_cap sg - ulen sg ->
  drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg <> [] ->
  dlater cx sg jb a tl ->
  dpfut cx sg 0 jb a (drain_b_c.da_ev a) (drain_b_c.da_erecs a) tl.
Proof.
  intros cx sg jb a tl Hw Hs Hg He Hp (fuel & Hn & Hw1 & Ht & Hf).
  destruct (dneed_dnext (dlive cx) (dxmx cx) sg Hg Hp Hw Hs He) as (Hd & Hwn).
  destruct fuel as [|f]; [lia|].
  rewrite (drun_data f (dlive cx) (dxmx cx) sg jb a Hg He Hp Hs) in Ht, Hf.
  cbn [fst snd] in Ht, Hf. subst tl.
  unfold dpfut. cbv beta zeta.
  rewrite firstn_O, skipn_O, dtm_lines_nil, dtm_feed_nil, dtm_pcapm_nil.
  cbn [length Z.of_nat]. rewrite Z.add_0_r.
  eexists. split. 2: reflexivity.
  unfold drfut. eexists. split. 2: reflexivity.
  unfold dlfut. cbv beta zeta. eexists. split. 2: reflexivity.
  match goal with |- context [danext ?ab ?r] =>
    replace (danext ab r) with (dnext_a (dlive cx) (dxmx cx) sg jb a)
      by (unfold dnext_a, danext, dapush; destruct (dwhole sg); reflexivity) end.
  unfold dlater. exists f. split; [lia|]. split; [exact Hwn|]. split; [reflexivity | exact Hf].
Qed.

Lemma dtm_den_gsh : forall E c, ew E 8 = Z_to_bv 64 (rg_s RG) -> 0 <= c -> rg_s RG + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff 8 c) (SLit 3)) = Z_to_bv 64 ((rg_s RG + c) / 8).
Proof.
  intros E c Hn Hc Hlt. pose proof HGSB as (G1 & _).
  rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E 8 (rg_s RG) c Hn ltac:(lia) ltac:(lia)), U_SLit, (zcanon_id 3) by (unfold M64; lia).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma dtm_gsh_ok : forall E (W1 : world SEGS) m1 base off c,
  ew E 8 = Z_to_bv 64 (rg_s RG) -> 0 <= c <= 4 * ASRC ->
  val_mem SEGS (arm W1 m1) (base + off) 8 ((rg_s RG + c) / 8) ->
  YP09.chunk_ok SEGS E (arm W1 m1) base (YP09.mkChunk off (dts_gsh c)).
Proof.
  intros E W1 m1 base off c H8 Hc Hv.
  pose proof HGSB as (G1 & G2 & _).
  assert (Hlt : rg_s RG + c < 2 ^ 64) by (unfold ASRC, IMG_TOP in *; lia).
  unfold dts_gsh.
  apply (chunk_ok_val SEGS E (arm W1 m1) base off 8 (SAlu ALU_SRL (SOff 8 c) (SLit 3)) ((rg_s RG + c) / 8)).
  - exact (dtm_den_gsh E c H8 ltac:(lia) Hlt).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  - zside.
  - exact Hv.
Qed.

Lemma dtm_chunks_ok : forall cx (W1 : world SEGS) m1 E,
  dr_frame RG cx W1 m1 -> ew E 8 = Z_to_bv 64 (rg_s RG) -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (YP09.chunk_ok SEGS E (arm W1 m1) (dsp0 cx - DRAIN_FRAME)) dts_chunks.
Proof.
  intros cx W1 m1 E HF H8 H32.
  destruct HF as (_ & _ & F40 & F48 & F56 & F64 & F72 & F80 & _ & F104 & _ & _ & _ & _ & F152 &
    _ & _ & _ & _ & _ & _ & _ & F240 & _).
  unfold dts_chunks.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F40].
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F48].
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F56].
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F64].
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F72].
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F80].
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F104].
  - apply dtm_gsh_ok; [exact H8 | unfold ASRC; lia | exact F152].
  - apply (chunk_ok_val SEGS E (arm W1 m1) (dsp0 cx - DRAIN_FRAME) 240 8 (SOff 32 0) SHADOW_OFF).
    + exact (den_atom0 E 32 SHADOW_OFF H32 ltac:(unfold SHADOW_OFF; lia)).
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold SHADOW_OFF. lia.
    + zside.
    + exact F240.
Qed.

Lemma dtm_frame_wr : forall cx ly1 S1 (W1 : world SEGS) m1 md1 k1 o,
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
  0 <= o < DRAIN_FRAME -> writable_at SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o).
Proof.
  intros cx ly1 S1 W1 m1 md1 k1 o HJ Ho.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  assert (HFS : (DRAIN_FRAME <=? DRAIN_STK) = true) by reflexivity.
  apply Z.leb_le in HFS.
  unfold arm. apply apresent_writable. apply Hpres. lia.
Qed.

Lemma dtm_frame_ok : forall cx (W1 : world SEGS) m1 E regs1,
  dr_frame RG cx W1 m1 -> spZ regs1 = dsp0 cx - DRAIN_FRAME -> ew E 2 = getr regs1 2 ->
  ew E 8 = Z_to_bv 64 (rg_s RG) -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  4096 <= dxSA cx -> dxSA cx + AENT <= alloc_ceiling -> alloc_ceiling + DRAIN_STK <= dsp0 cx ->
  dsp0 cx <= 2 ^ 47 ->
  region_ok SEGS E (arm W1 m1) dts_frame.
Proof.
  intros cx W1 m1 E regs1 HF Hsp H2 H8 H32 HSA1 HSA2 Hst Htop.
  assert (Hb : base_val E (Some 2%nat) = dsp0 cx - DRAIN_FRAME) by (cbn [base_val]; rewrite H2; exact Hsp).
  assert (HFS : (DRAIN_FRAME <=? DRAIN_STK) = true) by reflexivity.
  apply Z.leb_le in HFS.
  assert (HFV : DRAIN_FRAME = 352) by reflexivity.
  assert (HAE : AENT = 56) by reflexivity.
  unfold region_ok, dts_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Hb.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  exact (dtm_chunks_ok cx W1 m1 E HF H8 H32).
Qed.

Lemma dtm_framew_ok : forall cx (W1 : world SEGS) m1 E regs1,
  dr_frame RG cx W1 m1 -> spZ regs1 = dsp0 cx - DRAIN_FRAME -> ew E 2 = getr regs1 2 ->
  ew E 8 = Z_to_bv 64 (rg_s RG) -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  4096 <= dxSA cx -> dxSA cx + AENT <= alloc_ceiling -> alloc_ceiling + DRAIN_STK <= dsp0 cx ->
  dsp0 cx <= 2 ^ 47 ->
  (forall o, 16 <= o < 200 -> writable_at SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o)) ->
  region_ok SEGS E (arm W1 m1) dts_framew.
Proof.
  intros cx W1 m1 E regs1 HF Hsp H2 H8 H32 HSA1 HSA2 Hst Htop HW.
  assert (Hb : base_val E (Some 2%nat) = dsp0 cx - DRAIN_FRAME) by (cbn [base_val]; rewrite H2; exact Hsp).
  assert (HFS : (DRAIN_FRAME <=? DRAIN_STK) = true) by reflexivity.
  apply Z.leb_le in HFS.
  assert (HFV : DRAIN_FRAME = 352) by reflexivity.
  assert (HAE : AENT = 56) by reflexivity.
  unfold region_ok, dts_framew. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Hb.
  split; [lia|]. split; [lia|]. split; [exact HW|].
  exact (dtm_chunks_ok cx W1 m1 E HF H8 H32).
Qed.


End c2.

Section c3.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Definition dtk_low (cx : dcx) (a : Z) : Prop := 0 <= a < alloc_ceiling /\ ~ (dxG cx <= a < dxG cx + ATABLE).

Lemma dtk_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dtk_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dtk_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dtk_errno_sep : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (dtk_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (dtk_zpw _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dtk_zpw _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dtk_zpw _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dtk_zpw _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dtk_zpw _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dtk_zpw _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dtk_zpw _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dtk_zpw _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

Lemma dtk_low_img : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> 0x10000 <= a < IMG_TOP -> dtk_low cx a.
Proof.
intros cx ly S W mem md a HAR Hin Ha.
pose proof (blk_off_imgP B ly S W mem md _ _ HAR Hin) as Ho. red in Ho.
pose proof asan_consts as (C1 & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Ho.
unfold dtk_low, ATABLE, IMG_TOP in *. lia.
Qed.

Lemma dtk_low_blk : forall cx ly S (W : world SEGS) mem md L p n a,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dtk_low, ATABLE; lia|].
intros He. apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dtk_gs_ok : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md a HAR Hin Ha. pose proof HGSB as (G1 & G2 & _).
split; [apply (dtk_low_img cx ly S W mem md a HAR Hin); unfold ASRC in *; lia|].
apply dtk_errno_sep. left. exact Ha.
Qed.

Lemma dtk_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dtk_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dtk_fp_entry : forall cx ly S (W : world SEGS) mem md e L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dtk_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dtk_key_ptrs_len in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dtk_fp_list : forall cx ly S (W : world SEGS) mem md L LA l lines,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dtk_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dtk_gs_ok cx ly S W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dtk_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dtk_fp_src : forall cx ly S (W : world SEGS) mem md L h,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dtk_gs_ok cx ly S W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dtk_low_blk cx ly S W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dtk_fp_list cx ly S W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dtk_fp_list cx ly S W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dtk_fp_list cx ly S W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Lemma dtk_fp_out : forall cx ly S (W : world SEGS) mem md c O mx no cap out L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, 0x10000 <= x < 0x5fc000 -> dtk_low cx x)
  by (intros x Hx; apply (dtk_low_img cx ly S W mem md x HAR GT); unfold IMG_TOP; exact Hx).
assert (GDR : forall x, inG (G_DR B RG) x -> 0x10000 <= x < 0x5fc000)
  by (intros x Hx; exact (pa_img_range _ (proj1 (HG x Hx)))).
pose proof (pa_obj_img 9 ltac:(lia)) as P9. rewrite HV9 in P9.
pose proof HSM as (Hs1 & Hs2). pose proof HSD as (Hd1 & Hd2). unfold IMG_TOP in Hs2, Hd2.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [apply IMG; lia | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dtk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dtk_low_blk cx ly S W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

Lemma dtk_aout_ev : forall ly S (W : world SEGS) m m' c O mx no cap out ev,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W m W m' a) ->
(cap <> 0 -> forall a, out <= a < out + cap -> ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W m') (as_errno B) 4 ev -> awr W m' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
aout_at B RG ly S W m' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev) O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out ev
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HOB VE WE Hev.
assert (KC : forall a n, In (a, a + n) (aout_fp B RG cap out) -> forall x, a <= x < a + n ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W m W m' x)
  by (intros a n Hin x Hx Hne; exact (HK (a, a + n) Hin x Hx Hne)).
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H1]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H2]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H3]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H4]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H5]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H6]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H7]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H8]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H9]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H10]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H11]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H12]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H13]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H14]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H15]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dtk_errno_sep; repeat (first [left; lia | right]); lia] | exact H16]|].
split; [exact VE|]. split; [exact WE|]. split; [exact Hev|].
do 6 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W m); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold aout_fp; rewrite Ec; repeat (first [left; reflexivity | right]) | lia | apply (HOB ltac:(lia)); lia].
Qed.

Lemma dtk_perm_mv : forall (x : Z * Z) l1 l2 l3 r, Permutation (x :: l1 ++ l2 ++ l3 ++ r) (l1 ++ l2 ++ l3 ++ x :: r).
Proof. intros. rewrite !app_assoc. apply Permutation_middle. Qed.

Lemma dtk_aentry_blks_in : forall ly S (W : world SEGS) m e,
aentry_okx B ly S W m e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W m e (_ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hkeys) b Hb.
unfold aentry_blks in Hb.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
  + apply in_map_iff in Hb as (k & <- & Hk).
    rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
  + destruct Hb as [<- | Hb].
    * destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
- destruct Hb as [<- | Hb].
  + destruct Hbuf as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
    * destruct Hb as [<- | Hb].
      -- destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
      -- apply in_map_iff in Hb as (k & <- & Hk).
         rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
Qed.

Lemma dtk_alist_blks_in : forall ly S (W : world SEGS) m LA l lines,
alist_at B ly S W m LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W m LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
- destruct Hb as [<- | Hb].
  + destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
Qed.

Lemma dtk_asrc_blks_in : forall ly S (W : world SEGS) m HA h,
asrc_at B ly S W m HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W m HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
  Hexp & Hheld & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dtk_alist_blks_in ly S W m (HA + 16) (hs_pending h) false Hpend b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dtk_alist_blks_in ly S W m (HA + 64) (hs_expected h) true Hexp b Hb)
  |exact (dtk_alist_blks_in ly S W m (HA + 80) (hs_held h) true Hheld b Hb)].
Qed.

Lemma dtk_aout_blks_in : forall ly S (W : world SEGS) m c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W m c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.

Lemma dtk_aentry_okx_kept : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e,
aentry_okx B ly S W m e -> akept W m W' m' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) -> aentry_okx B ly' S' W' m' e.
Proof.
intros ly S W m ly' S' W' m' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

Lemma dtk_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H KL. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (KL x Hx).
Qed.

Lemma dtk_DMEM_kept : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM B RG cx ly1 S1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 HMEM HJ2 KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (Hkept : forall a, abyte_kept W1 m1 W1 m2 a).
{ intros a. split; [exact (KL a)|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKA : forall fp, akept W1 m1 W1 m2 fp) by (intros fp r Hr a Ha; exact (Hkept a)).
assert (HVM : forall a n v, val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v H. apply (akept_vm W1 m1); [intros x Hx; exact (Hkept x) | exact H]. }
split; [exact HJ2|].
split; [intros a Ha; rewrite (KL a); exact (Hrom a Ha)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  repeat match type of HFR with _ /\ _ => let A := fresh "A" in destruct HFR as [A HFR] end.
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVM; assumption | intros i Hi; apply HVM; exact (HFR i Hi) ]. }
split; [exact (dtk_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => KL x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact (dtk_aentry_okx_kept ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  (dtk_aentry_blks_in ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  (dtk_asrc_blks_in ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact (dtk_aout_blks_in ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.

Definition dtk_set_eintr (h : hsrc) : hsrc :=
HS (hs_fd h) (hs_open h) (hs_closed h) 0 (hs_pending h) (hs_off h) (hs_partial h) (hs_pjunk h)
  (hs_npartial h) (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).

Lemma dtk_blk_off : forall ly S (W : world SEGS) mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + n ->
0 <= a < 2 ^ 64 /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros ly S W mem md p n a HAR Hin Ha.
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & _).
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Ho. red in Ho.
pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
pose proof asan_consts as (C1 & _).
pose proof HGSB as (G1 & G2 & _). unfold IMG_TOP, ASRC in *.
split; lia.
Qed.

Lemma dtk_alist_kept : forall ly S (W : world SEGS) m m' LA l lines,
alist_at B ly S W m LA l lines ->
(forall x, LA <= x < LA + 16 -> abyte_kept W m W m' x) ->
(forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + n -> abyte_kept W m W m' x) ->
alist_at B ly S W m' LA l lines.
Proof.
intros ly S W m m' LA l lines HL KH KB.
apply (alist_at_kept B ly S W m ly S W m' LA l lines HL); [|exact (dtk_alist_blks_in ly S W m LA l lines HL)].
intros r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [apply KH; cbn [fst snd] in Ha; lia|].
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app, dtk_recs_len in Ha.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (KB (hl_v l) (AREC * hl_cap l)); [exact Hin | unfold hl_n, AREC in *; lia].
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
  rewrite Forall_forall in Hrecs.
  apply (KB (fst q) (Z.of_nat (length (snd q)) + 1)); [exact (proj1 (Hrecs q Hq)) | lia].
Qed.

Lemma dtk_asrc_set_eintr : forall ly S (W : world SEGS) m m' md HA h,
AR SEGS B ly S W m md -> rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
asrc_at B ly S W m HA h ->
val_mem SEGS (arm W m') (HA + 12) 4 0 -> awr W m' (HA + 12) 4 ->
(forall x, HA <= x < HA + ASRC -> ~ (HA + 12 <= x < HA + 16) -> abyte_kept W m W m' x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (HA <= x < HA + ASRC) -> abyte_kept W m W m' x) ->
asrc_at B ly S W m' HA (dtk_set_eintr h).
Proof.
intros ly S W m m' md HA h HAR Hlo Hhi HS VE WE KIN KOUT.
assert (KB : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + n -> abyte_kept W m W m' x).
{ intros p n x Hin Hx. destruct (dtk_blk_off ly S W m md p n x HAR Hin Hx) as (Hx1 & Hx2).
  apply KOUT; [exact Hx1 | lia]. }
assert (KS : forall lo, HA <= lo -> lo + 16 <= HA + 96 -> HA + 16 <= lo ->
  forall x, lo <= x < lo + 16 -> abyte_kept W m W m' x).
{ intros lo H1 H2 H3 x Hx. apply KIN; [unfold ASRC; lia | lia]. }
assert (Hvm : forall a n v, HA <= a -> a + Z.of_nat n <= HA + 12 \/ HA + 16 <= a -> a + Z.of_nat n <= HA + 96 ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v).
{ intros a n v H1 H2 H3 Hv. apply (akept_vm W m); [|exact Hv]. intros x Hx. apply KIN; [unfold ASRC; lia | lia]. }
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
  H19 & H20 & H21 & H22 & H23 & H24).
unfold asrc_at, dtk_set_eintr.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
  hs_expected hs_held].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H3]|].
split; [exact VE|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i 12) as [Hi1|Hi1].
  - apply (proj2 (KIN (HA + i) ltac:(lia) ltac:(lia))). exact (H5 i Hi).
  - destruct (Z_lt_le_dec i 16) as [Hi2|Hi2].
    + replace (HA + i) with (HA + 12 + (i - 12)) by lia. exact (WE (i - 12) ltac:(lia)).
    + apply (proj2 (KIN (HA + i) ltac:(lia) ltac:(lia))). exact (H5 i Hi). }
split; [exact H6|]. split; [left; reflexivity|]. split; [exact H8|]. split; [exact H9|].
split; [exact (dtk_alist_kept ly S W m m' (HA + 16) (hs_pending h) false H10
  (KS (HA + 16) ltac:(lia) ltac:(lia) ltac:(lia)) KB)|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|]. split; [exact H18|]. split; [exact H19|].
split.
{ apply (akept_garr8 W m); [|exact H20]. intros x Hx. apply (KB (hs_partial h) APARTIAL x H18).
  unfold bzs in Hx. rewrite length_map in Hx. lia. }
split; [exact H21|].
split; [exact (dtk_alist_kept ly S W m m' (HA + 64) (hs_expected h) true H22
  (KS (HA + 64) ltac:(lia) ltac:(lia) ltac:(lia)) KB)|].
split; [exact (dtk_alist_kept ly S W m m' (HA + 80) (hs_held h) true H23
  (KS (HA + 80) ltac:(lia) ltac:(lia) ltac:(lia)) KB)|].
exact H24.
Qed.

Definition dtk_eblks_rest (e : rentry) : list (Z * Z) :=
(if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e).

Lemma dtk_eblks_split : forall e,
aentry_blks e = (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++ dtk_eblks_rest e.
Proof. intros e. reflexivity. Qed.

Lemma dtk_perm2 : forall (X b c : Z * Z) l1 l2 L,
Permutation (X :: (b :: l1 ++ c :: l2) ++ L) (b :: c :: X :: l1 ++ l2 ++ L).
Proof.
intros X b c l1 l2 L. cbn [app]. rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
eapply Permutation_trans; [apply perm_skip; apply Permutation_sym; apply Permutation_middle|].
apply perm_swap.
Qed.

Lemma dtk_blk_sep : forall ly S (W : world SEGS) mem md X b R L p n,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (X :: (b :: R) ++ L) -> In (p, n) R ->
zdisjoint (block_rng b) (block_rng (p, n)).
Proof.
intros ly S W mem md X b R L p n HAR HP Hin.
destruct (in_split _ _ Hin) as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md b (p, n) (X :: l1 ++ l2 ++ L) HAR).
exact (Permutation_trans HP (dtk_perm2 X b (p, n) l1 l2 L)).
Qed.

Lemma dtk_aentry_junk : forall ly S (W : world SEGS) m m' md e (J : list byte) X L,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (X :: aentry_blks e ++ L) ->
aentry_okx B ly S W m e -> length J = length (re_junk e) ->
garr8 SEGS (arm W m') (re_buf e) (bzs (re_U e ++ J)) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (re_buf e + re_used e <= x < re_buf e + re_cap e) -> abyte_kept W m W m' x) ->
aentry_okx B ly S W m' (RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e)
  (re_hp e) (re_kh e) (re_pad2 e) (re_keys e) (re_U e) J).
Proof.
intros ly S W m m' md e J X L HAR HP HE HJ HGJ HK.
assert (KB : forall p n x, In (p, n) (dtk_eblks_rest e) -> p <= x < p + n -> abyte_kept W m W m' x).
{ intros p n x Hin Hx.
  pose proof HE as (_ & _ & _ & _ & _ & _ & HU & HUC & _).
  assert (Hab : In (p, n) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). right. apply in_or_app. left.
    rewrite dtk_eblks_split. apply in_or_app. right. exact Hin. }
  destruct (al_blocks SEGS B LAWS ly S W m md p n HAR Hab) as (_ & Hp4 & Hpc & _).
  pose proof asan_consts as (C1 & _).
  pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
  apply HK; [lia|].
  destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; [lia|].
  rewrite dtk_eblks_split, (proj2 (Z.eqb_neq _ _) Hc0) in HP.
  pose proof (dtk_blk_sep ly S W m md X (re_buf e, re_cap e) (dtk_eblks_rest e) L p n HAR HP Hin) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrc).
  lia. }
unfold aentry_okx in HE |- *.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
destruct HE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & _)]; [left; exact H9 | right].
  split; [exact Hc|]. split; [exact Hin|]. split; [rewrite HJ; exact Hj | exact HGJ]. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11 | right].
  split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (KB (re_hp e) (re_kh e)).
  - unfold dtk_eblks_rest. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  - unfold bzs in Hx. rewrite length_map, dtk_key_ptrs_len in Hx. unfold re_nheld in Hk1. lia. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [exact K1|]. split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (KB (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
- unfold dtk_eblks_rest. apply in_or_app. right.
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
- unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma dtk_aout_kept : forall ly S (W : world SEGS) m m' c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> abyte_kept W m W m' a) ->
aout_at B RG ly S W m' c O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out H HK.
exact (aout_at_kept B RG ly S W m ly S W m' c O mx no cap out H HK
  (dtk_aout_blks_in ly S W m c O mx no cap out H)).
Qed.


End c3.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.


Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

Lemma dt1_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dt1_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dt1_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dt1_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dt1_gs_sep : forall a,
(rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
 rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
 rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
 rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
 as_errno B <= a < as_errno B + 4) ->
~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros a Ha Hgs.
pose proof (dt1_zpw _ 2 3 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dt1_zpw _ 2 4 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dt1_zpw _ 2 5 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dt1_zpw _ 2 6 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dt1_zpw _ 2 7 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dt1_zpw _ 2 8 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dt1_zpw _ 2 9 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dt1_zpw _ 2 10 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
pose proof (dt1_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D11.
cbn [nth] in D3, D4, D5, D6, D7, D8, D9, D10, D11. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

Lemma dt1_fp_entry_gs : forall ly S (W : world SEGS) mem md e,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros ly S W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> p <= a < p + n ->
  ~ (rg_s RG <= a < rg_s RG + 4 * ASRC)).
{ intros p n Hin Hpa.
  exact (proj2 (dtk_blk_off B RG LAWS HGSB ly S W mem md p n a HAR
    (dtk_aentry_blks_in B RG HGSB ly S W mem e HE _ Hin) Hpa)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [|lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dt1_key_ptrs_len in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [|lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [|lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). exact Hk.
Qed.

Lemma dt1_fp_out_gs : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha;
  try (apply dt1_gs_sep; repeat first [left; lia | right]; lia).
destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
exact (proj2 (dtk_blk_off B RG LAWS HGSB ly S W mem md out cap a HAR Hin ltac:(lia))).
Qed.

Lemma dt1_blk_args : forall ly S (W : world SEGS) mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + n ->
0 <= a < alloc_ceiling /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros ly S W mem md p n a HAR Hin Ha.
destruct (dtk_blk_off B RG LAWS HGSB ly S W mem md p n a HAR Hin Ha) as (H64 & Hgs).
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
pose proof (@ASAN_CEIL_range rc) as (Hc & _). unfold ASAN_CEIL in Hceil.
split; [lia|]. split; [exact Hgs|].
intros He. apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dt1_rom_img : forall x, in_rom SEGS x -> in_img SEGS x.
Proof. intros x (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

Lemma dt1_frame_kept : forall cx (W1 : world SEGS) m m',
dr_frame RG cx W1 m ->
(forall o n v, 0 <= o -> o + Z.of_nat n <= DRAIN_FRAME ->
   val_mem SEGS (arm W1 m) (dsp0 cx - DRAIN_FRAME + o) n v ->
   val_mem SEGS (arm W1 m') (dsp0 cx - DRAIN_FRAME + o) n v) ->
dr_frame RG cx W1 m'.
Proof.
intros cx W1 m m' HFR HVM.
unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
repeat match type of HFR with _ /\ _ => let A := fresh "A" in destruct HFR as [A HFR] end.
unfold dr_saved in HFR |- *.
repeat match goal with |- _ /\ _ => split end;
  try (apply HVM; [lia | cbn; unfold DRAIN_FRAME; lia | assumption]).
intros i Hi. specialize (HFR i Hi).
replace (dsp0 cx - DRAIN_FRAME + DR_SAVE_OFF + 8 * Z.of_nat i)
  with (dsp0 cx - DRAIN_FRAME + (DR_SAVE_OFF + 8 * Z.of_nat i)) in HFR |- * by lia.
apply HVM; [unfold DR_SAVE_OFF; lia | cbn; unfold DRAIN_FRAME, DR_SAVE_OFF; lia | exact HFR].
Qed.

Definition dt1_hs : YP09.region :=
YP09.mkRegion (Some 23%nat) 12 16 12 16 [ YP09.mkChunk 12 (CVal 4 (SLit 1)) ].
Definition dt1_facts (j : nat) : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, dts_IMGF);
  (19%nat, mkAF (SHADOW_OFF + 12 * Z.of_nat j) (SHADOW_OFF + 12 * Z.of_nat j) 0);
  (23%nat, dts_IMGF); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition dt1_ss (j : nat) : sstate :=
mkSS A_dr_slot sr_atoms [ dts_frame; dt1_hs ] None (dt1_facts j).
Definition dt1_extra : list word := [ Z_to_bv 64 SHADOW_OFF ].
Definition dt1_SH2 : list shent := [ mkSHE 37 0 4 ].

Lemma dt1_mod8 : forall g (j : nat), g mod 8 = 0 -> (g + ASRC * Z.of_nat j) mod 8 = 0.
Proof.
intros g j H. unfold ASRC. rewrite Z.add_mod by lia. rewrite H.
replace (96 * Z.of_nat j) with ((12 * Z.of_nat j) * 8) by lia. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma dt1_seat : forall cx (W : world SEGS) regs m,
DBASE B MT MMAX RG cx ->
spZ regs = dsp0 cx - DRAIN_FRAME ->
getr regs 8 = w64 (rg_s RG) -> getr regs 23 = w64 (dHA RG cx) ->
getr regs 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
dr_frame RG cx W m ->
val_mem SEGS (arm W m) (dHA RG cx + 12) 4 1 ->
awr W m (dHA RG cx) ASRC ->
st_ok_pi SEGS VAL (Eimg (Ereg regs dt1_extra)) (dt1_ss (dxj cx))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_slot)) m (seg_rom SEGS))).
Proof.
intros cx W regs m HB Hsp R8 R23 R19 HFR VEI HAW.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs dt1_extra)).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs dt1_extra 0)).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E2 : ew E 2 = getr regs 2) by (apply EREG; [lia | reflexivity]).
assert (U2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG)
  by (rewrite E8; apply unsigned_lit_small; unfold IMG_TOP, ASRC in *; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small;
      unfold dHA, ASRC, IMG_TOP in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HHA : 0x10000 <= dHA RG cx /\ dHA RG cx + ASRC <= IMG_TOP) by (unfold dHA, ASRC, IMG_TOP in *; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, dts_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    exact (dtm_chunks_ok B RG HGSB cx W m E HFR E8 E32).
  + unfold region_ok, dt1_hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [lia|]. split; [unfold IMG_TOP, ASRC in *; lia|].
    split; [intros o Ho; exact (HAW o ltac:(unfold ASRC; lia))|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 12 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia | exact VEI].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, dts_frame, dt1_hs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23.
  split; [split; [right; unfold IMG_TOP, ASRC in *; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]].
  unfold dt1_facts, dts_IMGF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U19, U23, U32.
  assert (M16 : (dsp0 cx - DRAIN_FRAME) mod 2 ^ 4 = 0)
    by (change (2 ^ 4) with 16; rewrite HDF, Zminus_mod, Hal16; reflexivity).
  assert (M8 : rg_s RG mod 2 ^ 3 = 0) by exact G3.
  assert (M23 : dHA RG cx mod 2 ^ 3 = 0) by (unfold dHA; exact (dt1_mod8 (rg_s RG) (dxj cx) G3)).
  rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
    unfold IMG_TOP, SHADOW_OFF, ASRC in *; lia.
Qed.

Lemma dt1_dctl_ev : forall cx tot ev1 ev,
CTL (ct_cl (dctl cx tot ev1)) (ct_br (dctl cx tot ev1)) (ct_dd (dctl cx tot ev1))
  (ct_ei (dctl cx tot ev1)) ev = dctl cx tot ev.
Proof.
intros cx tot ev1 ev. unfold dctl. cbv zeta. cbn [ct_cl ct_br ct_dd ct_ei]. reflexivity.
Qed.

Lemma dt1_dmem : forall cx sg ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
   ~ (as_errno B <= x < as_errno B + 4) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
asrc_at B ly1 S1 W1 mF (dHA RG cx) (dtk_set_eintr h1) ->
val_mem SEGS (arm W1 mF) (as_errno B) 4 4 ->
DMEM B RG cx ly1 S1 W1 mF mdF k1 e1 (dtk_set_eintr h1) (dclr sg) out1 4 sent LB1.
Proof.
intros cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF HB HMEM HJF KEEP PRES HSRCF VERR.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
pose proof asan_consts as (C1 & _). pose proof HGSB as (GS1 & GS2 & GS3).
assert (HDS : DRAIN_STK = 16880) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HspA : alloc_ceiling + DRAIN_STK <= dsp0 cx) by lia.
assert (HspB : dsp0 cx <= 2 ^ 47) by lia.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
  by (unfold dHA, ASRC; lia).
assert (GIMG : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GSG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (ERG : forall x, as_errno B <= x < as_errno B + 4 -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]).
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= IMG_TOP).
{ pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B) ltac:(lia)))) as P0.
  pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B + 3) ltac:(lia)))) as P3. unfold IMG_TOP. lia. }
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept (w_H W1) m1 mF x (PRES x) Hw)).
assert (KI : forall x, 0x10000 <= x < IMG_TOP -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx N1 N2. split; [apply KEEP; [unfold IMG_TOP in *; lia | exact N1 | exact N2
    | unfold IMG_TOP in *; lia] | unfold arm; apply writable_kept; apply PRES]. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. split; [apply KEEP;
    [lia | unfold dHA, ASRC, IMG_TOP in *; lia | unfold IMG_TOP in *; lia | lia]
  | unfold arm; apply writable_kept; apply PRES]. }
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> q <= x < q + n -> abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hx.
  destruct (dt1_blk_args ly1 S1 W1 m1 md1 q n x HAR Hin Hx) as (Hc & Hgs & Hne).
  split; [apply KEEP; [lia | unfold dHA, ASRC in *; lia | exact Hne | lia]
  | unfold arm; apply writable_kept; apply PRES]. }
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
pose proof HEOK as (_ & _ & Hpad1 & Hpad2 & _).
split; [exact HJF|].
split.
{ intros x Hx. rewrite KEEP; [exact (Hrom x Hx)
  | pose proof (pa_img_range _ (dt1_rom_img x Hx)); lia
  | intros Hy; apply (HGR x); [apply GSG; unfold dHA, ASRC in *; lia | exact Hx]
  | intros Hy; apply (HGR x); [apply ERG; exact Hy | exact Hx]
  | pose proof (pa_img_range _ (dt1_rom_img x Hx)); unfold IMG_TOP in *; lia]. }
split; [intros x Hx1 Hx2 Hx3 Hx4; apply PRES; exact (Hpres x Hx1 Hx2 Hx3 Hx4)|].
split; [exact Hframes|].
split.
{ apply (dt1_frame_kept cx W1 m1 mF HFR).
  intros o n v Ho Hn Hv. apply (akept_vm W1 m1); [intros x Hx; apply KFR; lia | exact Hv]. }
split.
{ apply (dtk_garr8_kept W1 m1 W1 mF _ _ Hgarr). intros x Hx.
  unfold bzs in Hx. rewrite length_map in Hx.
  unfold entry_bytes, re_nheld in Hx.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, Hpad1, Hpad2 in Hx.
  exact (proj1 (KBL (dxG cx) ATABLE x HGin1 ltac:(unfold AENT, ATABLE in *; lia))). }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ apply (dtk_aentry_okx_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF e1 HEOK);
    [|exact (dtk_aentry_blks_in B RG HGSB ly1 S1 W1 m1 e1 HEOK)].
  intros r Hr x Hx.
  destruct (dtk_fp_entry B RG LAWS HG HGSB cx ly1 S1 W1 m1 md1 e1
    (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)
    HAR Hperm (fun b Hb => in_or_app _ _ _ (or_introl Hb)) HEOK r Hr x Hx) as (Hlow & Hne).
  pose proof (dt1_fp_entry_gs ly1 S1 W1 m1 md1 e1 HAR HEOK r Hr x Hx) as Hgs.
  destruct Hlow as (Hx0 & _).
  split; [apply KEEP; [lia | unfold dHA, ASRC in *; lia | exact Hne | lia]
  | unfold arm; apply writable_kept; apply PRES]. }
split; [exact HSRCF|].
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KI;
      [unfold ASRC, IMG_TOP in *; lia | unfold dHA, ASRC in *; lia
      | apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); left; unfold ASRC in *; lia].
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KI;
      [unfold ASRC, IMG_TOP in *; lia | unfold dHA, ASRC in *; lia
      | apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); left; unfold ASRC in *; lia]. }
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as K1.
  assert (K2 : abyte_kept W1 m1 W1 mF x)
    by (apply KI; [unfold ASRC, IMG_TOP in *; lia | unfold ASRC in *; lia
        | apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); left; exact Hx1]).
  split; [rewrite (proj1 K2); exact (proj1 K1)|].
  intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw. }
split.
{ pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AWERR & _).
  rewrite <- (dt1_dctl_ev cx (Z.of_nat (length (with_nul sent))) ev1 4).
  refine (dtk_aout_ev B RG HRGD HGSB HSD HSM ly1 S1 W1 m1 mF _ _ _ _ _ _ 4 Hout _ _ VERR _ _).
  - intros r Hr x Hx Hne.
    destruct (dtk_fp_out B MMAX RG LAWS HG HRGD HGSB HMMAX HV9 HSD HSM cx ly1 S1 W1 m1 md1 _ _ _ _ _ _
      (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)
      HAR Hperm
      (fun b Hb => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb))))))
      Hout r Hr x Hx) as (Hlow & _).
    pose proof (dt1_fp_out_gs ly1 S1 W1 m1 md1 _ _ _ _ _ _ HAR Hout r Hr x Hx) as Hgs.
    destruct Hlow as (Hx0 & _).
    split; [apply KEEP; [lia | unfold dHA, ASRC in *; lia | exact Hne | lia]
    | unfold arm; apply writable_kept; apply PRES].
  - intros Hc x Hx.
    assert (Hin : In (out1, drain_b_c.ds_ocap sg) (ablocks B ly1 S1)).
    { apply (dtk_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout). unfold aout_blks.
      rewrite (proj2 (Z.eqb_neq _ 0) Hc). left. reflexivity. }
    exact (proj2 (proj2 (dt1_blk_args ly1 S1 W1 m1 md1 out1 (drain_b_c.ds_ocap sg) x HAR Hin Hx))).
  - intros i Hi. apply HWK. exact (AWERR i Hi).
  - lia. }
split; [exact Hlivout | exact Hperm].
Qed.

Lemma dt1_eintr : forall cx sg D W1 c1,
DBASE B MT MMAX RG cx -> DT2 B MT MMAX RG cx sg D W1 c1 ->
drain_b_c.ds_eintr sg = true ->
(forall W2 c2, DI B MT MMAX RG cx (dclr sg) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx sg D W1 c1 HB HT HEI K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
assert (HDS : DRAIN_STK = 16880) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
destruct HT as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & HRG & R23 & R19 & R10 & R13 & HM & HNZ & HUS & HDB & HL & HSAME & HH & HJ1 & HROOM & HLAT & HBUD).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HM as (HJ & HROM & HAPK & HFRS & HFR & HEB & HEW & HEX & HSRC & HOTH & HGK & HOUT & HDEAD & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & HSTK0 & _).
pose proof HSTK0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HSPA : alloc_ceiling + DRAIN_STK <= dsp0 cx) by lia.
assert (HSPB : dsp0 cx <= 2 ^ 47) by lia.
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
pose proof HL as (_ & _ & _ & _ & _ & HLE & _).
rewrite HEI in HLE.
pose proof HSRC as (_ & _ & _ & VEI & HAW & _).
rewrite HLE in VEI.
pose proof (dt1_seat cx W1 regs1 m1 HB Hsp R8 R23 R19 HFR VEI HAW) as HS.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
remember (Eimg (Ereg regs1 dt1_extra)) as E eqn:HE.
assert (HEIE : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 dt1_extra 0)).
assert (UB1 : U E dts_Bx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dts_Bx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19
      | unfold SHADOW_OFF; lia]).
assert (U8 : U E (SOff 8 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8
      | unfold IMG_TOP, ASRC in *; lia]).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small;
      unfold dHA, ASRC, IMG_TOP in *; lia).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (SHOK : sh_ok SEGS dts_Bx1 dts_SHgs E (mrestrict (w_H W1) m1))
  by exact (dts_shent_gs B RG LAWS HGSZ HGSB ly1 S1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U8).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
revert HS. destruct (dxj cx) as [|[|[|[|jj]]]] eqn:Ej; [| | | | exfalso; lia]; intros HS.
all: paj_run_tok RUN HS HJ SHOK dts_Bspan;
  [ cbn [ss_mem dt1_ss];
    apply awr_ok_x_cons;
    [ intros x Hx; exfalso; cbn [dts_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia | ];
    apply awr_ok_x_cons_g; [ | apply awr_ok_x_nil ];
    intros x Hx; cbn [dt1_hs YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U23 in Hx;
    unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold dHA, ASRC in *; lia | ].
all: pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as RF1; cbn [ms_mem restrict] in RF1.
all: assert (V12A : val_mem SEGS (arm W1 (ms_mem ms)) (dHA RG cx + 12) 4 0);
  [ unfold arm;
    pose proof (field_of_region E (mrestrict (w_H W1) (ms_mem ms)) 23%nat (dHA RG cx) _ 12 16 12 16 12
      4%N (SLit 0) 0 RF1) as VF;
    apply VF; [exact U23 | left; reflexivity | reflexivity | cbn; lia | cbn; lia] | ].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
all: eapply SRr_bind;
  [ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
    [ unfold spZ at 1; rewrite Q2, Usp; lia
    | reflexivity
    | unfold DRAIN_FRAME; lia
    | lia
    | unfold ESTACK, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | rewrite Q3, (EREG 3%nat 3%bv), R3 by (first [lia | reflexivity]); exact Hgp
    | rewrite Q4, (EREG 4%nat 4%bv), R4 by (first [lia | reflexivity]); exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros x; right; intros []
    | intros x []
    | intros x []
    | intros HPRE2 _; exact (AERRNO ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ HPRE2) ] |].
all: cbv beta; intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
all: jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0]%nat HS2.
all: match type of HS2 with ?ty -> _ =>
  assert (HRK : ty) by
    (cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
     split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros aa Haa;
     [ apply (mbyte_of_aview SEGS); apply Hfr2;
       [ lia | intros [] | lia ]
     | exfalso; lia ]);
  specialize (HS2 HRK); clear HRK end.
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 33 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
all: assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEIE | cbv; lia]).
all: assert (OLDa : forall n, (n < 33)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
all: clear HEa.
all: pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAWE & _).
all: prreg HS (10%bv : bv 5) R10a.
all: assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= IMG_TOP);
  [ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i));
    [ intros i Hi; apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
        repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ])))
    | pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0;
      pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3; unfold IMG_TOP; lia ] | ].
all: assert (F37 : ew Ea 37 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10a, Herr, HERRNO; reflexivity).
all: assert (B37 : bv_unsigned (ew Ea 37) = as_errno B)
  by (rewrite F37; apply unsigned_lit_small; unfold IMG_TOP in *; lia).
all: apply (st_ok_pi_add_fact _ _ _ 37%nat (mkAF 0x10000 IMG_TOP 2)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B37;
     split; [unfold IMG_TOP in *; lia|]; split; [change (2 ^ 2) with 4; exact HERRAL | lia] ].
all: apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 37%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B37; split; [unfold IMG_TOP in *; lia|]; split; [unfold IMG_TOP in *; lia|];
      split; [|apply Forall_nil];
      intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
      [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (HAWE o Ho) ]
    | cbn [ss_mem add_atom all_disjoint]; unfold extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite B37, (OLDa 2%nat ltac:(lia)), Usp;
      split; [left; unfold IMG_TOP in *; lia | exact I] ].
all: assert (UB2 : U Ea dts_Bx2 = SHADOW_OFF)
  by (unfold dts_Bx2; apply U_atom;
      [ rewrite (OLDa 32%nat) by lia; exact E32 | unfold SHADOW_OFF; lia ]).
all: assert (UE37 : U Ea (SOff 37 0) = as_errno B)
  by (apply U_atom; [exact F37 | unfold IMG_TOP in *; lia]).
all: assert (SHOK2 : sh_ok SEGS dts_Bx2 dt1_SH2 Ea (mrestrict (w_H W1) mem2));
  [ unfold sh_ok, dt1_SH2; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dts_Bx2 37%nat (as_errno B) 4 (as_errno B) 0 4);
    [ apply (azs_range_addressable B LAWS ly1 S1 W1 mem2 md2 (as_errno B) 4);
      [ exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) | exact HERRZ ]
    | exact UB2 | exact UE37 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF, IMG_TOP in *; lia ] | ].
all: paj_run_to_tok RUNTO HS HJ2 SHOK2 dts_Bspan A_dr_top;
  [ cbn [ss_mem];
    apply awr_ok_x_cons_g;
    [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite B37 in Hx;
      unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
    | apply awr_ok_x_cons;
      [ intros x Hx; exfalso;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
      | apply awr_ok_x_nil ] ] | ].
all: rename HFr into FR3; rename HG0 into GR3; clear HF.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: assert (KL2 : forall x, 0 <= x < 2 ^ 64 -> ~ (as_errno B <= x < as_errno B + 4) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) mem2 x);
  [ intros x Hx0 Hx; apply (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms0) FR3 x Hx0);
    intros (r & Hin & Hr); cbn [ss_mem add_atom In] in Hin; destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [ rewrite B37 in Hr; lia | lia ] | ].
all: assert (KL1 : forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x);
  [ intros x Hx0 Hx; apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 x Hx0);
    intros (r & Hin & Hr); cbn [ss_mem dt1_ss In] in Hin; destruct Hin as [<- | [<- | []]];
    unfold dts_frame, dt1_hs in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [ lia | rewrite U23 in Hr; lia ] | ].
all: assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ (as_errno B <= x < as_errno B + 4) ->
  ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) (ms_mem ms) x);
  [ intros x H1 H2 H3; rewrite (KL2 x H1 H2); apply Hfr2; [exact H1 | intros [] | lia] | ].
all: assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  ~ (as_errno B <= x < as_errno B + 4) ->
  ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) m1 x);
  [ intros x H1 H2 H3 H4; rewrite (KEEP2 x H1 H3 H4); exact (KL1 x H1 H2) | ].
all: assert (PRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms0) x);
  [ intros x Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2;
    apply (apresent_grows _ _ _ _ GR1); exact Hp | ].
all: assert (AWR12 : awr W1 (ms_mem ms) (dHA RG cx + 12) 4);
  [ intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 (ms_mem ms));
    [ apply (apresent_grows _ _ _ _ GR1) | ];
    replace (dHA RG cx + 12 + i) with (dHA RG cx + (12 + i)) by lia;
    exact (HAW (12 + i) ltac:(unfold ASRC; lia)) | ].
all: assert (HSRCA : asrc_at B ly1 S1 W1 (ms_mem ms) (dHA RG cx) (dtk_set_eintr h1));
  [ apply (dtk_asrc_set_eintr B RG LAWS HGSB ly1 S1 W1 m1 (ms_mem ms) md1 (dHA RG cx) h1 HAR
      ltac:(unfold dHA, ASRC; lia) ltac:(unfold dHA, ASRC; lia) HSRC V12A AWR12);
    [ intros x Hx N; split;
      [ apply KL1; [unfold dHA, ASRC, IMG_TOP in *; lia | exact N]
      | unfold arm; apply writable_kept; apply (apresent_grows _ _ _ _ GR1) ]
    | intros x Hx N; split;
      [ apply KL1; [exact Hx | unfold dHA, ASRC in *; lia]
      | unfold arm; apply writable_kept; apply (apresent_grows _ _ _ _ GR1) ] ] | ].
all: assert (HSRCF : asrc_at B ly1 S1 W1 (ms_mem ms0) (dHA RG cx) (dtk_set_eintr h1));
  [ apply (asrc_at_kept B ly1 S1 W1 (ms_mem ms) ly1 S1 W1 (ms_mem ms0) (dHA RG cx)
      (dtk_set_eintr h1) HSRCA);
    [ intros r Hr x Hx;
      destruct (dtk_fp_src B RG LAWS HG HRGD HGSB HSD HSM cx ly1 S1 W1 m1 md1
        (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)
        h1 HAR HPERM (fun b Hb => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb))))
        HGin ltac:(rewrite Ej; lia) HSRC r Hr x Hx) as ((Hx0 & _) & Hne);
      split; [ exact (KEEP2 x ltac:(lia) Hne ltac:(lia))
             | unfold arm; apply writable_kept;
               intros Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2; exact Hp ]
    | intros b Hb; exact (dtk_asrc_blks_in B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 HSRC b Hb) ] | ].
all: assert (VERR : val_mem SEGS (arm W1 (ms_mem ms0)) (as_errno B) 4 4);
  [ unfold arm;
    pose proof (field_of_region _ (mrestrict (w_H W1) (ms_mem ms0)) 37%nat (as_errno B) _ 0 4 0 4 0
      4%N (SLit 4) 4 RF) as VF;
    rewrite Z.add_0_r in VF; apply VF;
    [ rewrite !ew_ewset_other by lia; exact B37 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] | ].
all: pose proof (dt1_dmem cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1
  (ms_mem ms0) (with_vm_backing (m_vm_lazy md2) mat0 md2) HB HM HJ2 KEEP PRES HSRCF VERR) as HM2.
all: pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
all: assert (HLF : DLINK (dclr sg) e1 (dtk_set_eintr h1));
  [ unfold DLINK, dclr, dtk_set_eintr;
    cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
         drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en
         drain_b_c.ds_ecap hs_eintr hs_pending hs_off hs_expected];
    split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|];
    split; [exact L5|]; split; [reflexivity|]; split; [exact L7|]; split; [exact L8|];
    split; [exact L9|]; split; [exact L10|]; split; [exact L11 | exact L12] | ].
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4;
  prreg HS (8%bv : bv 5) X8; prreg HS (9%bv : bv 5) X9; prreg HS (18%bv : bv 5) X18;
  prreg HS (20%bv : bv 5) X20; prreg HS (21%bv : bv 5) X21; prreg HS (22%bv : bv 5) X22;
  prreg HS (24%bv : bv 5) X24; prreg HS (26%bv : bv 5) X26; prreg HS (27%bv : bv 5) X27.
all: pmkst HS.
all: apply K.
all: exists (ms_regs ms0), ly1, S1, (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2), k1, e1,
  (dtk_set_eintr h1), out1, 4, LB1, spent, jb, a, tl.
all: split; [reflexivity|].
all: split;
  [ split; [unfold spZ; rewrite X2, OLDa by lia;
            rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|];
    split; [rewrite X3, OLDa by lia; rewrite (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|];
    split; [rewrite X4, OLDa by lia; rewrite (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|];
    split; [rewrite X21, OLDa by lia; rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|];
    split; [rewrite X24, OLDa by lia; rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24|];
    split; [rewrite X20, OLDa by lia; rewrite (EREG 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|];
    split; [rewrite X22, OLDa by lia; rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); exact R22|];
    split; [rewrite X27, OLDa by lia; rewrite (EREG 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|];
    split; [rewrite X8, OLDa by lia; rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|];
    split; [rewrite X9, OLDa by lia; rewrite (EREG 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|];
    split; [rewrite X18, OLDa by lia; rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|];
    rewrite X26, OLDa by lia; rewrite (EREG 26%nat 26%bv) by (first [lia | reflexivity]); exact R26 | ].
all: split; [exact HM2|].
all: split; [exact HNZ|].
all: split; [exact HUS|].
all: split; [intros _; exact HDB|].
all: split; [exact HLF|].
all: split; [exact HSAME|].
all: split; [exact HH|].
all: split; [exact HJ1|].
all: split; [exact (dtm_later_dclr B RG HGSB cx sg jb a tl L12 HROOM HEI HLAT) | exact HBUD].
Qed.



Definition dt2_hs (ei pn : Z) : YP09.region :=
YP09.mkRegion (Some 23%nat) 12 28 12 12 [ YP09.mkChunk 12 (CVal 4 (SLit ei)); YP09.mkChunk 24 (CVal 4 (SLit pn)) ].
Definition dt2_facts (j : nat) : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, dts_IMGF);
  (19%nat, mkAF (SHADOW_OFF + 12 * Z.of_nat j) (SHADOW_OFF + 12 * Z.of_nat j) 0);
  (23%nat, dts_IMGF); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition dt2_ss (j : nat) (ei pn : Z) : sstate :=
mkSS A_dr_slot sr_atoms [ dts_frame; dt2_hs ei pn ] None (dt2_facts j).
Definition dt2_extra : list word := [ Z_to_bv 64 SHADOW_OFF ].

Lemma dt2_mod8 : forall g (j : nat), g mod 8 = 0 -> (g + ASRC * Z.of_nat j) mod 8 = 0.
Proof.
intros g j H. unfold ASRC. rewrite Z.add_mod by lia. rewrite H.
replace (96 * Z.of_nat j) with ((12 * Z.of_nat j) * 8) by lia. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma dt2_seat : forall cx (W : world SEGS) regs m (ei pn : Z),
DBASE B MT MMAX RG cx ->
spZ regs = dsp0 cx - DRAIN_FRAME ->
getr regs 8 = w64 (rg_s RG) -> getr regs 23 = w64 (dHA RG cx) ->
getr regs 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
dr_frame RG cx W m ->
val_mem SEGS (arm W m) (dHA RG cx + 12) 4 ei -> 0 <= ei < 2 ^ 32 ->
val_mem SEGS (arm W m) (dHA RG cx + 24) 4 pn -> 0 <= pn < 2 ^ 32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs dt2_extra)) (dt2_ss (dxj cx) ei pn)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_slot)) m (seg_rom SEGS))).
Proof.
intros cx W regs m ei pn HB Hsp R8 R23 R19 HFR VEI HEI VPN HPN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs dt2_extra)).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs dt2_extra 0)).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E2 : ew E 2 = getr regs 2) by (apply EREG; [lia | reflexivity]).
assert (U2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG)
  by (rewrite E8; apply unsigned_lit_small; unfold IMG_TOP, ASRC in *; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small;
      unfold dHA, ASRC, IMG_TOP in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HHA : 0x10000 <= dHA RG cx /\ dHA RG cx + ASRC <= IMG_TOP) by (unfold dHA, ASRC, IMG_TOP in *; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, dts_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    exact (dtm_chunks_ok B RG HGSB cx W m E HFR E8 E32).
  + unfold region_ok, dt2_hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [lia|]. split; [unfold IMG_TOP, ASRC in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ _ 12 4 (SLit ei) ei); [reflexivity | cbn; lia | cbn; lia | exact VEI].
    * apply (chunk_ok_val SEGS E _ _ 24 4 (SLit pn) pn); [reflexivity | cbn; lia | cbn; lia | exact VPN].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, dts_frame, dt2_hs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23.
  split; [split; [right; unfold IMG_TOP, ASRC in *; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]].
  unfold dt2_facts, dts_IMGF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U19, U23, U32.
  assert (M16 : (dsp0 cx - DRAIN_FRAME) mod 2 ^ 4 = 0)
    by (change (2 ^ 4) with 16; rewrite HDF, Zminus_mod, Hal16; reflexivity).
  assert (M8 : rg_s RG mod 2 ^ 3 = 0) by exact G3.
  assert (M23 : dHA RG cx mod 2 ^ 3 = 0) by (unfold dHA; exact (dt2_mod8 (rg_s RG) (dxj cx) G3)).
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
    unfold IMG_TOP, SHADOW_OFF, ASRC in *; lia.
Qed.

Lemma dt2_end : forall cx sg D W1 c1,
DBASE B MT MMAX RG cx -> DT2 B MT MMAX RG cx sg D W1 c1 ->
drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg = [] ->
(forall W2 c2, DEND B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx sg D W1 c1 HB HT HEF HPD K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
destruct HT as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & HRG & R23 & R19 & R10 & R13 & HM & HNZ & HUS & HDB & HL & HSAME & HH & HJ1 & HROOM & HLAT & HBUD).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HM as (HJ & _ & _ & _ & HFR & _ & _ & _ & HSRC & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HL as (_ & _ & _ & _ & _ & HLE & _).
rewrite HEF in HLE.
assert (HREC : hl_recs (hs_pending h1) = []) by exact (proj1 (dts_pend_recs sg e1 h1 HL) HPD).
pose proof HSRC as (_ & _ & _ & VEI & _ & _ & _ & _ & _ & HPL & _).
pose proof HPL as (_ & VPN & _).
rewrite HLE in VEI.
unfold hl_n in VPN. rewrite HREC in VPN. cbn [length Z.of_nat] in VPN.
replace (dHA RG cx + 16 + 8) with (dHA RG cx + 24) in VPN by lia.
pose proof (dt2_seat cx W1 regs1 m1 0 0 HB Hsp R8 R23 R19 HFR VEI ltac:(lia) VPN ltac:(lia)) as HS.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
remember (Eimg (Ereg regs1 dt2_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (UB1 : U E dts_Bx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dts_Bx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19
      | unfold SHADOW_OFF; lia]).
assert (U8 : U E (SOff 8 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8
      | unfold IMG_TOP, ASRC in *; lia]).
assert (SHOK : sh_ok SEGS dts_Bx1 dts_SHgs E (mrestrict (w_H W1) m1))
  by exact (dts_shent_gs B RG LAWS HGSZ HGSB ly1 S1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U8).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
revert HS. destruct (dxj cx) as [|[|[|[|jj]]]] eqn:Ej; [| | | | exfalso; lia]; intros HS.
all: paj_run_to_tok RUNTO HS HJ SHOK dts_Bspan A_dr_end; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: assert (KL : forall x, aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x);
  [ intros x; apply (aview_eq_of SEGS); apply FR1; intros (r & Hin & Hr);
    cbn [ss_mem dt2_ss In] in Hin; destruct Hin as [<- | [<- | []]];
    unfold dts_frame, dt2_hs in Hr; cbn [YP09.r_wlo YP09.r_whi] in Hr; lia | ].
all: assert (KP : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR1 Hp)).
all: pose proof (dtk_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms) md1 _ k1 k1 e1 h1 sg out1 ev1 _ LB1 HM HJ KL KP)
  as HM2.
all: pose proof HM2 as (_ & _ & _ & _ & HFR2 & _).
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4;
  prreg HS (19%bv : bv 5) X19; prreg HS (21%bv : bv 5) X21; prreg HS (23%bv : bv 5) X23.
all: pmkst HS.
all: apply K.
all: exists (ms_regs ms), ly1, S1, (ms_mem ms), (with_vm_backing (m_vm_lazy md1) mat md1), k1, e1, h1, out1, ev1, LB1,
  spent, jb, a, tl.
all: split; [reflexivity|].
all: split; [unfold spZ; rewrite X2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
all: split; [rewrite X3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
all: split; [rewrite X4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
all: split; [rewrite X21, (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
all: split; [rewrite X23, (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23|].
all: split; [rewrite X19, (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite Ej; exact R19|].
all: split; [exact HFR2|].
all: split; [exact HM2|].
all: exact (conj HNZ (conj HUS (conj HL (conj HSAME (conj HH (conj HJ1 (conj HPD (conj HEF (conj HROOM
  (conj HLAT HBUD)))))))))).
Qed.


Definition dt3_sh1 : Z := AF_fr_drain + 0x2b4.
Definition dt3_sh2 : Z := AF_fr_drain + 0x338.
Definition dt3_sh3 : Z := AF_fr_drain + 0x350.
Definition dt3_sh4 : Z := AF_fr_drain + 0x390.
Definition dt3_pc_n : Z := AF_fr_drain + 0x3b0.
Definition dt3_pc_cpy : Z := AF_fr_drain + 0x3e4.
Definition dt3_pc_ret : Z := AF_fr_drain + 0x3e8.
Definition dt3_pc_drb : Z := AF_fr_drain + 0x484.

#[local] Notation dt3_shA m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 32 0)).

Definition dt3_w (lo : Z) : YP09.region := YP09.mkRegion (Some 2%nat) lo (lo + 8) lo (lo + 8) [].
Definition dt3_f48 : YP09.region := YP09.mkRegion (Some 2%nat) 48 72 0 0
[ YP09.mkChunk 48 (dts_gsh 56); YP09.mkChunk 56 (dts_gsh 48); YP09.mkChunk 64 (dts_gsh 40) ].
Definition dt3_f72 : YP09.region := YP09.mkRegion (Some 2%nat) 72 88 0 0
[ YP09.mkChunk 72 (dts_gsh 32); YP09.mkChunk 80 (dts_gsh 16) ].
Definition dt3_f104 : YP09.region := YP09.mkRegion (Some 2%nat) 104 112 0 0 [ YP09.mkChunk 104 (dts_gsh 24) ].
Definition dt3_f152 : YP09.region := YP09.mkRegion (Some 2%nat) 152 160 0 0 [ YP09.mkChunk 152 (dts_gsh 12) ].
Definition dt3_f240 : YP09.region := YP09.mkRegion (Some 2%nat) 240 248 0 0
[ YP09.mkChunk 240 (CVal 8 (SOff 32 0)) ].
Definition dt3_slot : YP09.region := YP09.mkRegion (Some 23%nat) 0 96 0 0
[ YP09.mkChunk 12 (CVal 4 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
  YP09.mkChunk 24 (CVal 4 (SOff 33 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0)) ].
Definition dt3_rec : YP09.region := YP09.mkRegion (Some 34%nat) 0 16 0 0
[ YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0)) ].

Definition dt3_SPF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition dt3_SBF : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
Definition dt3_facts1 : facts := mkFacts
[ (2%nat, dt3_SPF); (8%nat, dts_IMGF); (23%nat, dts_IMGF); (32%nat, dt3_SBF);
  (33%nat, mkAF 1 (2 ^ 30) 0); (34%nat, dts_HEAPF);
  (35%nat, mkAF 1 (2 ^ 47) 0); (36%nat, mkAF 0 (2 ^ 47) 0); (37%nat, dts_HEAPF);
  (38%nat, mkAF 1 16384 0) ] [] [].
Definition dt3_ss1 : sstate :=
mkSS A_dr_slot dts_regs
  [dt3_w 24; dt3_w 96; dt3_w 112; dt3_w 160; dt3_w 168; dt3_w 192;
   dt3_f48; dt3_f72; dt3_f104; dt3_f152; dt3_f240; dt3_slot; dt3_rec] None dt3_facts1.
Definition dt3_SH : list shent := [ mkSHE 23 0 96; mkSHE 34 0 16 ].
Definition dt3_x1 (n v len off p dn : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; n; v; len; off; p; dn].

Lemma dt3_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof.
intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. reflexivity.
Qed.

Lemma dt3_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma dt3_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0)))
  by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, dt3_nth_zle by exact Hk. rewrite dt3_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma dt3_val_of_garr8 : forall (m : word -> option byte) a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS m a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS m a n v.
Proof.
intros m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat)
  by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS m a _ k H Hl). rewrite dt3_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma dt3_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Lemma dt3_rec_vm : forall (m : word -> option byte) v r0 rs J,
garr8 SEGS m v (bzs (concat (map text_rec (r0 :: rs)) ++ J)) ->
0 <= fst r0 < 2 ^ 64 -> Z.of_nat (length (snd r0)) < 2 ^ 64 ->
val_mem SEGS m v 8 (fst r0) /\ val_mem SEGS m (v + 8) 8 (Z.of_nat (length (snd r0))).
Proof.
intros m v r0 rs J H H1 H2.
cbn [map concat] in H. unfold text_rec in H.
rewrite (dt3_le8_bytes (fst r0)) in H by lia.
rewrite (dt3_le8_bytes (Z.of_nat (length (snd r0)))) in H by lia.
unfold bzs in H. rewrite !map_app in H. rewrite <- !app_assoc in H.
apply garr8_app in H as (Ha & Hb). apply garr8_app in Hb as (Hb & _).
rewrite length_map, length_Z_to_le_bytes in Hb.
split; apply dt3_val_of_garr8; first [lia | assumption].
Qed.

Lemma dt3_mod_addk : forall a k m, m <> 0 -> a mod m = 0 -> (a + k * m) mod m = 0.
Proof. intros a k m Hm Ha. rewrite Z.mod_add by exact Hm. exact Ha. Qed.

Lemma dt3_U_gsh : forall E g c, ew E 8 = Z_to_bv 64 g -> 0 <= g < 2 ^ 64 -> 0 <= g + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff 8 c) (SLit 3)) = (g + c) / 8.
Proof.
intros E g c Hn Hg Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 8 g c Hn Hg Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma dt3_U_shA : forall E (m : nat) w c, ew E m = Z_to_bv 64 w -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
0 <= w < 2 ^ 64 -> 0 <= w + c < 2 ^ 47 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 32 0)) = shadow_addr (w + c).
Proof.
intros E m w c Hn H32 Hw Hc. unfold shadow_addr. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E m w c Hn Hw ltac:(lia)), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (w + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((w + c) / 8)) by (unfold M64; lia).
rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; lia).
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma dt3_den_shA : forall E (m : nat) w c, ew E m = Z_to_bv 64 w -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
0 <= w < 2 ^ 64 -> 0 <= w + c < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (shadow_addr (w + c)).
Proof.
intros E m w c Hn H32 Hw Hc. rewrite denot_lit_U. f_equal. exact (dt3_U_shA E m w c Hn H32 Hw Hc).
Qed.

Lemma dt3_den_resh : forall E g j c,
ew E 8 = Z_to_bv 64 g -> ew E 19 = Z_to_bv 64 (SHADOW_OFF + 12 * j) ->
ew E 23 = Z_to_bv 64 (g + 96 * j) -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
0 <= g -> 0 <= j -> 0 <= c -> g + 96 * j + c < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 c) (SLit 3)) (SOff 19 0)) =
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 c) (SLit 3)) (SOff 32 0)).
Proof.
intros E g j c H8 H19 H23 H32 Hg Hj Hc Hb.
rewrite !denot_lit_U. f_equal.
rewrite (dt3_U_shA E 23 (g + 96 * j) c H23 H32) by lia.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (dt3_U_gsh E g c H8) by lia.
rewrite (U_atom E 19 (SHADOW_OFF + 12 * j) H19) by (unfold SHADOW_OFF; lia).
unfold shadow_addr.
replace (g + 96 * j + c) with ((g + c) + (12 * j) * 8) by lia. rewrite Z.div_add by lia.
assert (Hd : 0 <= (g + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

Lemma dt3_sh_range : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 64.
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.


Lemma dt3_seat1 : forall cx (W1 : world SEGS) m1 regs1 n v len off p dn,
dregs_top RG cx regs1 -> getr regs1 23 = w64 (dHA RG cx) ->
(dxj cx < 4)%nat -> 4096 <= dxSA cx -> dxSA cx + AENT <= alloc_ceiling ->
alloc_ceiling + DRAIN_STK <= dsp0 cx -> dsp0 cx <= 2 ^ 47 -> dsp0 cx mod 16 = 0 ->
dr_frame RG cx W1 m1 -> (forall o, 0 <= o < DRAIN_FRAME -> writable_at SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o)) ->
1 <= n < 2 ^ 30 -> 4096 <= v -> v + 16 <= alloc_ceiling -> v mod 8 = 0 ->
(v + 16 <= rg_s RG \/ rg_s RG + 4 * ASRC <= v) ->
1 <= len <= 2 ^ 47 -> 0 <= off <= 2 ^ 47 -> 4096 <= p <= 140737479966720 -> p mod 8 = 0 -> 1 <= dn <= 16384 ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 12) 4 0 -> val_mem SEGS (arm W1 m1) (dHA RG cx + 16) 8 v ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 24) 4 n -> val_mem SEGS (arm W1 m1) (dHA RG cx + 32) 8 off ->
val_mem SEGS (arm W1 m1) v 8 p -> val_mem SEGS (arm W1 m1) (v + 8) 8 len ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dt3_x1 n v len off p dn))) dt3_ss1
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_slot)) m1 (seg_rom SEGS))).
Proof.
intros cx W1 m1 regs1 n v len off p dn HR R23 Hj HSA1 HSA2 Hsp1 Hsp2 Hsp3 HF HW Hn Hv1 Hv2 Hv3 HvG
  Hl Ho Hp1 Hp2 Hdn V12 V16 V24 V32 VP VL.
pose proof HR as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HGSB as (G1 & G2 & G3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HAE : AENT = 56) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (dt3_x1 n v len off p dn))).
assert (EREG : forall (k : nat) (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ k r Hr)).
assert (EX : forall i, (i < 7)%nat -> ew E (32 + i) = nth i (dt3_x1 n v len off p dn) (Z_to_bv 64 0))
  by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ i)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E21 : ew E 21 = Z_to_bv 64 (dxSA cx)) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E23 : ew E 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 v) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 off) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 p) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 dn) by exact (EX 6%nat ltac:(lia)).
assert (HHA : dHA RG cx = rg_s RG + 96 * Z.of_nat (dxj cx)) by (unfold dHA, ASRC; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; unfold IMG_TOP, ASRC in *; lia).
assert (U21 : bv_unsigned (ew E 21) = dxSA cx) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx) by (rewrite E23; apply unsigned_lit_small; unfold IMG_TOP, ASRC in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = len) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = off) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = p) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = dn) by (rewrite E38; apply unsigned_lit_small; lia).
pose proof HF as (F8 & F32s & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152 &
  F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & FSV).
unfold dt3_ss1. apply pa_entry_st_ok_full.
- unfold dts_regs.
  repeat (apply regs_ok_pin; [ | intros X; discriminate X |
    first [ rewrite R27, (den_atom E 21 (dxSA cx) 32 E21) by lia; reflexivity
          | rewrite R22, (den_atom E 21 (dxSA cx) 24 E21) by lia; reflexivity
          | rewrite R20, (den_atom E 21 (dxSA cx) 16 E21) by lia; reflexivity
          | rewrite R24, (den_atom E 21 (dxSA cx) 8 E21) by lia; reflexivity ] ]).
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil;
    [ unfold region_ok, dt3_w | unfold region_ok, dt3_w | unfold region_ok, dt3_w
    | unfold region_ok, dt3_w | unfold region_ok, dt3_w | unfold region_ok, dt3_w
    | unfold region_ok, dt3_f48
    | unfold region_ok, dt3_f72 | unfold region_ok, dt3_f104 | unfold region_ok, dt3_f152
    | unfold region_ok, dt3_f240 | unfold region_ok, dt3_slot | unfold region_ok, dt3_rec ];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?Usp, ?U23, ?U34.
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply HW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply HW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply HW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply HW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply HW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply HW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (dtm_gsh_ok B RG HGSB E W1 m1 _ 48 56); [exact E8 | unfold ASRC; lia | exact F48].
    * apply (dtm_gsh_ok B RG HGSB E W1 m1 _ 56 48); [exact E8 | unfold ASRC; lia | exact F56].
    * apply (dtm_gsh_ok B RG HGSB E W1 m1 _ 64 40); [exact E8 | unfold ASRC; lia | exact F64].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (dtm_gsh_ok B RG HGSB E W1 m1 _ 72 32); [exact E8 | unfold ASRC; lia | exact F72].
    * apply (dtm_gsh_ok B RG HGSB E W1 m1 _ 80 16); [exact E8 | unfold ASRC; lia | exact F80].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (dtm_gsh_ok B RG HGSB E W1 m1 _ 104 24); [exact E8 | unfold ASRC; lia | exact F104].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (dtm_gsh_ok B RG HGSB E W1 m1 _ 152 12); [exact E8 | unfold ASRC; lia | exact F152].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 240 8 (SOff 32 0) SHADOW_OFF);
        [apply den_atom0; [exact E32 | unfold SHADOW_OFF; lia]
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | zside | exact F240].
  + split; [unfold IMG_TOP, ASRC in *; lia|]. split; [unfold IMG_TOP, ASRC in *; lia|].
    split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 12 4 (SLit 0) 0);
        [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside | exact V12].
    * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 34 0) v);
        [apply den_atom0; [exact E34 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact V16].
    * apply (chunk_ok_val SEGS E _ _ 24 4 (SOff 33 0) n);
        [apply den_atom0; [exact E33 | lia] | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside | exact V24].
    * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 36 0) off);
        [apply den_atom0; [exact E36 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact V32].
  + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 37 0) p);
        [apply den_atom0; [exact E37 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside
        | rewrite Z.add_0_r; exact VP].
    * apply (chunk_ok_val SEGS E _ _ 8 8 (SOff 35 0) len);
        [apply den_atom0; [exact E35 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact VL].
- cbn [pairwise_disjoint all_disjoint]. unfold YP09.extent_disjoint.
  cbn [dt3_w dt3_f48 dt3_f72 dt3_f104 dt3_f152 dt3_f240 dt3_slot dt3_rec
       YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, U23, U34. unfold IMG_TOP, ASRC in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [dt3_facts1 f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2 dt3_SPF dt3_SBF dts_IMGF dts_HEAPF].
  assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0).
  { replace (dsp0 cx - DRAIN_FRAME) with (dsp0 cx + (-22) * 16) by lia. apply dt3_mod_addk; [lia | exact Hsp3]. }
  assert (HHAm : dHA RG cx mod 8 = 0).
  { rewrite HHA. replace (rg_s RG + 96 * Z.of_nat (dxj cx)) with (rg_s RG + (12 * Z.of_nat (dxj cx)) * 8) by lia.
    apply dt3_mod_addk; [lia | exact G3]. }
  rewrite Usp, U8, U23, U32, U33, U34, U35, U36, U37, U38. unfold IMG_TOP, ASRC in *.
  repeat match goal with |- _ /\ _ => split end; try exact I;
    first [ lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | change (2 ^ 3) with 8; lia
          | change (2 ^ 4) with 16; exact Hspm | change (2 ^ 3) with 8; exact HHAm ].
Qed.

Lemma dt3_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma dt3_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma dt3_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dt3_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Definition dt3_apart (p n q m : Z) : Prop := p + n <= q \/ q + m <= p.

Lemma dt3_pw_in2 : forall {X} (R : X -> X -> Prop) l x y, YG0f.pairwise R l -> In x l -> In y l -> x <> y ->
R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
cbn [In YG0f.pairwise] in HP, Hx, Hy.
destruct HP as [HF HP]. rewrite Forall_forall in HF.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- exfalso; apply Hne; reflexivity.
- left. exact (HF y Hy).
- right. exact (HF x Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.

Lemma dt3_pw_nodup : forall l : list (Z * Z), (forall x, In x l -> 1 <= snd x) -> YG0f.pairwise zdisjoint l ->
List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hpw; [apply List.NoDup_nil|].
destruct Hpw as [Hx Hl]. apply List.NoDup_cons.
- intros Hin. rewrite Forall_forall in Hx. pose proof (Hx x Hin) as Hzz. pose proof (Hpos x (or_introl eq_refl)).
  unfold zdisjoint in Hzz. lia.
- apply IH; [intros y Hy; apply Hpos; right; exact Hy | exact Hl].
Qed.

Lemma dt3_nodup_map_inj : forall {X Y} (f : X -> Y) (l : list X) x y,
List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros X Y f l. induction l as [|z l IH]; intros x y Hnd Hx Hy Hf; [destruct Hx|].
cbn [map] in Hnd. inversion Hnd as [|w ws Hz Hnd']; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y Hnd' Hx Hy Hf)].
- exfalso. apply Hz. rewrite Hf. apply in_map. exact Hy.
- exfalso. apply Hz. rewrite <- Hf. apply in_map. exact Hx.
Qed.

Lemma dt3_blk_apart : forall ly S (W : world SEGS) mem md p n q m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
dt3_apart p (req_size n) q (req_size m).
Proof.
intros ly S W mem md p n q m HAR Hp Hq Hne.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
pose proof (dt3_pw_nodup _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros Eq; exact (Hne (dt3_nodup_map_inj f _ _ _ Hnd Hp Hq Eq))).
destruct (dt3_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hp) (in_map f _ _ Hq) Hf) as [X|X];
  unfold dt3_apart, zdisjoint, f in *; cbn [fst snd] in X; lia.
Qed.

Lemma dt3_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hp : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
rewrite <- Eb. exact (NoDup_map_inv f _ (dt3_pw_nodup _ Hpos Hpw)).
Qed.

Lemma dt3_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & H1 & _ & H3). exists sg. split; [exact H1 | exact H3]. Qed.

Lemma dt3_alist_fp_in : forall ly S (W : world SEGS) mem LA l lines,
alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall x, fst r <= x < snd r ->
(LA <= x < LA + 16) \/ exists q m, In (q, m) (alist_blks l) /\ q <= x < q + m.
Proof.
intros ly S W mem LA l lines HL r Hr x Hx.
pose proof HL as (_ & _ & _ & _ & Hnc & Hv & _ & _ & _).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Hx; exact Hx|].
right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []].
  unfold gfp in Hx. cbn [fst snd] in Hx.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (hl_v l), (AREC * hl_cap l). split.
  + unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). left. reflexivity.
  + assert (Hlen : Z.of_nat (length (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l)
      by (unfold bzs; rewrite length_map, length_app, dt3_recs_len; unfold AREC, hl_n in *; lia).
    lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Hx. cbn [fst snd] in Hx.
  exists (fst q), (Z.of_nat (length (snd q)) + 1). split.
  + unfold alist_blks. apply in_or_app. right. exact (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) _ _ Hq).
  + assert (Hlen : Z.of_nat (length (bzs (snd q ++ [Z_to_bv 8 0]))) = Z.of_nat (length (snd q)) + 1)
      by (unfold bzs; rewrite length_map, length_app; cbn [length]; lia).
    lia.
Qed.

Lemma dt3_asrc_fp_in : forall ly S (W : world SEGS) mem HA h, asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall x, fst r <= x < snd r ->
(HA <= x < HA + 96) \/ exists q m, In (q, m) (asrc_blks h) /\ q <= x < q + m.
Proof.
intros ly S W mem HA h HS r Hr x Hx.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Hx. unfold ASRC in Hx. lia.
- right. exists (hs_partial h), APARTIAL. split; [left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in Hx.
  assert (Hlen : Z.of_nat (length (bzs (hs_pjunk h))) = APARTIAL)
    by (unfold bzs; rewrite length_map; lia).
  lia.
- apply in_app_or in Hr as [Hr | Hr].
  + destruct (dt3_alist_fp_in _ _ _ _ _ _ _ Hpend r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
    exists q, m. split; [right; apply in_or_app; left; exact Hq | exact Hqx].
  + apply in_app_or in Hr as [Hr | Hr].
    * destruct (dt3_alist_fp_in _ _ _ _ _ _ _ Hexp r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx].
    * destruct (dt3_alist_fp_in _ _ _ _ _ _ _ Hheld r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hq | exact Hqx].
Qed.

Lemma dt3_aout_fp_in : forall cap out r, In r (aout_fp B RG cap out) -> forall x, fst r <= x < snd r ->
in_img SEGS x \/ exists q m, In (q, m) (aout_blks cap out) /\ q <= x < q + m.
Proof.
intros cap out r Hr x Hx.
assert (GD : forall b l, In (b, l) (G_DR B RG) -> b <= x < b + l -> in_img SEGS x).
{ intros b l Hb Hbx. apply (proj1 (HG x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
assert (GO : forall b l, In (b, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] ->
  b <= x < b + l -> in_img SEGS x).
{ intros b l Hb Hbx. apply (proj1 (HGO x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
unfold aout_fp in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
  cbn [fst snd] in Hx.
- left. apply (GO (rg_send_max RG) 8); [right; right; left; reflexivity | lia].
- left. apply (GD (rg_nout RG) 8); [right; right; right; left; reflexivity | lia].
- left. apply (GD (rg_capout RG) 8); [right; right; right; right; left; reflexivity | lia].
- left. apply (GD (rg_out RG) 8); [right; right; right; right; right; left; reflexivity | lia].
- left. apply (GO (rg_client RG) 4); [left; reflexivity | lia].
- left. apply (GD (rg_client_broken RG) 1); [right; left; reflexivity | lia].
- left. apply (GO (rg_send_dead RG) 1); [right; left; reflexivity | lia].
- left. apply (GD (rg_send_eintr RG) 1); [right; right; left; reflexivity | lia].
- left. apply (GD (as_errno B) 4); [right; right; right; right; right; right; left; reflexivity | lia].
- right. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  exists out, cap. split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc0); left; reflexivity | lia].
Qed.

Lemma dt3_garr8_aview : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j H Hj. pose proof (garr8_mbyte SEGS (arm W m) base l j H Hj) as Hm.
destruct (H j Hj) as (_ & Hr). unfold arm in Hm. unfold aview.
rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hr.
Qed.

Lemma dt3_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.

Lemma dt3_garr8_of_aview : forall (W : world SEGS) m a l,
(forall j, (j < length l)%nat -> aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0)) ->
Forall (fun b => 0 <= b < 256) l -> garr8 SEGS (arm W m) a l.
Proof.
intros W m a l HA HR j Hj. rewrite Forall_forall in HR.
pose proof (HR (nth j l 0) (nth_In l 0 Hj)) as Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0)%nat by lia. subst k.
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite dt3_le_byte1 by exact Hr.
pose proof (HA j Hj) as HAj. unfold arm, aview in *.
destruct (mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat j)) as [b|] eqn:Hb; [|discriminate HAj].
cbn [option_map] in HAj. injection HAj as HAj.
rewrite <- HAj. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma dt3_bzs_range : forall l, Forall (fun b => 0 <= b < 256) (bzs l).
Proof.
intros l. unfold bzs. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (x & <- & _).
unfold bz. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma dt3_skipn_bzs : forall k l, skipn k (bzs l) = bzs (skipn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. apply IH. Qed.
Lemma dt3_firstn_bzs : forall k l, firstn k (bzs l) = bzs (firstn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma dt3_garr8_skipn : forall m a l k, garr8 SEGS m a l -> (k <= length l)%nat ->
garr8 SEGS m (a + Z.of_nat k) (skipn k l).
Proof.
intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply garr8_app in H as [_ H].
rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Lemma dt3_nth_firstn : forall {A} k (l : list A) i d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
intros A k. induction k as [|k IH]; intros l i d H; [lia|].
destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma dt3_nth_skipn : forall {A} o (l : list A) i d, nth i (skipn o l) d = nth (o + i) l d.
Proof.
intros A o. induction o as [|o IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [rewrite skipn_nil; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma dt3_nth_data : forall (t : list byte) (z : byte) (o k i : nat), (o + k <= length t)%nat -> (i < k)%nat ->
nth (o + i) (bzs (t ++ [z])) 0 = nth i (bzs (firstn k (skipn o t))) 0.
Proof.
intros t z o k i Hl Hi. rewrite <- dt3_firstn_bzs, <- dt3_skipn_bzs, dt3_nth_firstn by exact Hi.
rewrite dt3_nth_skipn. unfold bzs. rewrite map_app. apply app_nth1. rewrite length_map. lia.
Qed.

Lemma dt3_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (bzs (entry_bytes e)) = 56%nat.
Proof.
intros e H1 H2. unfold bzs. rewrite length_map. unfold entry_bytes.
rewrite !length_app, H1, H2, !Mem.length_le8, !Mem.length_le4. reflexivity.
Qed.

Definition dt3_junk (e : rentry) (j : list byte) : rentry :=
RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e) (re_pad2 e)
   (re_keys e) (re_U e) j.

Lemma dt3_dmem_drb : forall cx sg ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF (data : list byte),
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
0 < re_cap e1 -> (length data <= length (re_junk e1))%nat ->
(forall x, 0 <= x < 2 ^ 64 ->
   ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
   ~ (dsp0 cx - DRAIN_STK <= x < dsp0 cx) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
(forall i, (i < length data)%nat ->
   aview SEGS (w_H W1) mF (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)) ->
dr_frame RG cx W1 mF ->
DMEM B RG cx ly1 S1 W1 mF mdF k1 (dt3_junk e1 (data ++ skipn (length data) (re_junk e1))) h1 sg out1 ev1 sent LB1.
Proof.
intros cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF data HB HMEM HJF Hcp Hdl KEEP PRES CPY HFRF.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & _ & Hj4 & _).
pose proof Hafn as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HDS : DRAIN_STK = 16880) by reflexivity.
assert (HspA : alloc_ceiling + 16880 <= dsp0 cx) by (unfold dsp0; rewrite HDS in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
pose proof HGSB as (GS1 & GS2 & GS3).
pose proof HEOK as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
  HND1 & HND2 & Hkeys).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [lia|].
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & _). rewrite RQC in Hbceil.
assert (Hboff : YCbq.off_img (re_buf e1) (re_cap e1)).
{ pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as X.
  rewrite RQC in X. exact X. }
assert (HDL : Z.of_nat (length data) <= re_cap e1 - re_used e1) by (rewrite <- Hjl; lia).
assert (Hul : 0 <= re_used e1) by lia.
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> (q, n) <> (re_buf e1, re_cap e1) -> q <= x < q + n ->
  abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hne Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos n ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0); lia)) as (_ & Rq).
  pose proof (dt3_blk_apart _ _ _ _ _ _ _ _ _ HAR Hin Hbin Hne) as Hap. rewrite RQC in Hap.
  split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; unfold dt3_apart in *; lia. }
assert (KI : forall x, in_img SEGS x -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. pose proof (pa_img_range x Hx) as Hr.
  split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; unfold YCbq.off_img in Hboff; lia. }
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept _ m1 mF x (PRES x) Hw)).
pose proof (Permutation_NoDup Hperm (dt3_ablocks_nodup _ _ _ _ _ HAR)) as HNDp.
unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by lia. cbn [app] in HNDp.
apply List.NoDup_cons_iff in HNDp as [HGnot HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot _].
assert (INB : forall b, In b (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). right. unfold aentry_blks.
  rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by lia. cbn [app]. right. exact Hb. }
assert (KH : forall q n x, In (q, n) (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> q <= x < q + n ->
    abyte_kept W1 m1 W1 mF x).
{ intros q n y Hb Hy. apply (KBL q n y (INB _ Hb)); [|exact Hy].
  intros Heq. apply Hbufnot. rewrite <- Heq. exact Hb. }
split; [exact HJF|].
split; [intros x Hx; rewrite (proj1 (KI x (dt3_rom_img x Hx))); exact (Hrom x Hx)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply PRES; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split; [exact HFRF|].
assert (KEEPB : forall x, 0 <= x < 2 ^ 64 ->
  ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
  ~ (dsp0 cx - DRAIN_STK <= x < dsp0 cx) -> abyte_kept W1 m1 W1 mF x)
  by (intros x Hx N1 N2; split; [apply KEEP; assumption | unfold arm; apply writable_kept; apply PRES]).
split.
{ replace (entry_bytes (dt3_junk e1 (data ++ skipn (length data) (re_junk e1)))) with (entry_bytes e1)
    by reflexivity.
  apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx.
  rewrite (dt3_entry_len e1 Hpad1 Hpad2) in Hx.
  apply (KBL (dxG cx) ATABLE x HGin1
    ltac:(intros X; injection X as X1 X2; unfold ATABLE in *; lia)
    ltac:(unfold AENT, ATABLE in *; lia)). }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ unfold aentry_okx, dt3_junk.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
  split; [exact Heof|]. split; [exact Hskip|]. split; [exact Hpad1|]. split; [exact Hpad2|].
  split; [exact Hfd|]. split; [exact Hcapr|]. split; [exact HUlen|]. split; [exact Husedc|].
  split.
  { right. split; [exact Hcpos|]. split; [exact Hbin|].
    split; [rewrite length_app, length_skipn; lia|].
    rewrite dt3_bzs_app in Hbuf8. apply garr8_app in Hbuf8 as [GU GJ].
    rewrite dt3_bzs_len, HUlen in GJ.
    rewrite !dt3_bzs_app. apply garr8_app. split.
    - apply (akept_garr8 W1 m1); [|exact GU]. intros x Hx. rewrite dt3_bzs_len in Hx.
      apply KEEPB; lia.
    - rewrite dt3_bzs_len, HUlen. apply garr8_app. split.
      + apply dt3_garr8_of_aview; [|apply (dt3_bzs_range data)].
        intros i Hi. rewrite dt3_bzs_len in Hi. exact (CPY i Hi).
      + rewrite dt3_bzs_len.
        pose proof (dt3_garr8_skipn _ _ _ (length data) GJ ltac:(rewrite dt3_bzs_len; exact Hdl)) as GJ'.
        rewrite dt3_skipn_bzs in GJ'.
        apply (akept_garr8 W1 m1); [|exact GJ']. intros x Hx.
        rewrite dt3_bzs_len, length_skipn in Hx. apply KEEPB; lia. }
  split; [exact Hnheld|].
  split.
  { destruct Hheld as [H0 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H0 | right].
    split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx.
    apply (KH (re_hp e1) (re_kh e1)); [apply in_or_app; left; apply in_or_app; left;
      rewrite (proj2 (Z.eqb_neq _ 0) Hz); left; reflexivity|].
    unfold bzs in Hx. rewrite length_map, dt3_key_ptrs_len in Hx. unfold re_nheld in Hk1. lia. }
  split; [exact HND1|]. split; [exact HND2|].
  rewrite Forall_forall in Hkeys |- *. intros k Hk. destruct (Hkeys k Hk) as (K1 & K2 & K3).
  split; [exact K1|]. split; [|exact K3].
  apply (akept_garr8 W1 m1); [|exact K2]. intros x Hx.
  apply (KH (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
  - apply in_or_app. left. apply in_or_app. right.
    exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hk).
  - unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia. }
assert (KGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. apply KI. apply (proj1 (HG x ltac:(unfold G_DR, inG; apply Exists_cons_hd;
    unfold in_zr; cbn [fst snd]; exact Hx))). }
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 4 * ASRC)
  by (unfold dHA, ASRC; lia).
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 mF (dHA RG cx) h1 Hsrc);
    [|exact (dtk_asrc_blks_in B RG HGSB ly1 S1 W1 m1 _ _ Hsrc)].
  intros r Hr x Hx. destruct (dt3_asrc_fp_in _ _ _ _ _ _ Hsrc r Hr x Hx) as [X | (q & n & Hq & Hqx)].
  - apply KGS. lia.
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. left. exact Hq. }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KGS. unfold ASRC in *. lia.
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KGS. unfold ASRC in *. lia. }
split.
{ intros x Hx1 Hx2. destruct (Hgsk x Hx1 Hx2) as (Kv & Kw). destruct (KGS x Hx1) as (Kv2 & Kw2).
  split; [rewrite Kv2; exact Kv | intros Hw; exact (Kw2 (Kw Hw))]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF); [exact Hout | |
    exact (dtk_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout)].
  intros r Hr x Hx. destruct (dt3_aout_fp_in _ _ r Hr x Hx) as [Hi | (q & n & Hq & Hqx)].
  - exact (KI x Hi).
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hq. }
split; [exact Hlivout | exact Hperm].
Qed.

Definition dt3_wfr (cx : dcx) (a : Z) : Prop :=
dsp0 cx - DRAIN_FRAME + 24 <= a < dsp0 cx - DRAIN_FRAME + 32 \/
dsp0 cx - DRAIN_FRAME + 96 <= a < dsp0 cx - DRAIN_FRAME + 104 \/
dsp0 cx - DRAIN_FRAME + 112 <= a < dsp0 cx - DRAIN_FRAME + 120 \/
dsp0 cx - DRAIN_FRAME + 160 <= a < dsp0 cx - DRAIN_FRAME + 168 \/
dsp0 cx - DRAIN_FRAME + 168 <= a < dsp0 cx - DRAIN_FRAME + 176 \/
dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200.

Lemma dt3_vm_kept : forall (W : world SEGS) m m' a (nn : nat) z,
(forall x, a <= x < a + Z.of_nat nn -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a nn z -> val_mem SEGS (arm W m') a nn z.
Proof.
intros W m m' a nn z KL H k Hk. unfold arm. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (KL (a + Z.of_nat k) ltac:(lia))).
exact (H k Hk).
Qed.

Lemma dt3_frame_kept : forall cx (W1 : world SEGS) m1 m2,
dr_frame RG cx W1 m1 -> alloc_ceiling + DRAIN_STK <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> ~ dt3_wfr cx a ->
   aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
dr_frame RG cx W1 m2.
Proof.
intros cx W1 m1 m2 HF Hsp1 Hsp2 KL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof HF as (F8 & F32s & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152 &
  F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & FSV).
unfold dr_frame. cbv zeta.
repeat (split; [apply (dt3_vm_kept W1 m1 m2);
  [ intros x Hx; apply KL; [lia | unfold dt3_wfr; lia]
  | first [exact F8 | exact F32s | exact F40 | exact F48 | exact F56 | exact F64 | exact F72 | exact F80
         | exact F88 | exact F104 | exact F120 | exact F128 | exact F136 | exact F144 | exact F152
         | exact F176 | exact F184 | exact F200 | exact F208 | exact F216 | exact F224 | exact F232
         | exact F240] ] |]).
intros i Hi. unfold DR_SAVE_OFF. apply (dt3_vm_kept W1 m1 m2);
  [ intros x Hx; apply KL; [lia | unfold dt3_wfr; lia] | unfold DR_SAVE_OFF in FSV; exact (FSV i Hi) ].
Qed.

Ltac dt3_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Ltac dt3_awr Usp :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha;
      first [ lia | left; split; [unfold awr_byte; left; lia | lia] ] |]);
  apply awr_ok_x_nil.

Ltac dt3_rs HS E HHA E8 E19 E23 E32 cxx r c :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    let Hx := fresh "Hx" in
    let Hd := fresh "Hd" in
    let HS' := fresh "HS'" in
    dt3_reg HS r Hx;
    assert (Hd : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 c) (SLit 3)) (SOff 32 0))
      = getr (ms_regs mx) r)
      by (rewrite Hx; symmetry;
          apply (dt3_den_resh E (rg_s RG) (Z.of_nat (dxj cxx)) c E8 E19 ltac:(rewrite <- HHA; exact E23) E32);
          unfold IMG_TOP, ASRC in *; lia);
    pose proof (ast_ok_pi_set_reg_fp E _ _ r _ HS eq_refl Hd) as HS';
    clear HS Hd Hx; rename HS' into HS;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS
  end.

Ltac dt3_trap Hc T := exfalso; rewrite T in Hc; discriminate.

Ltac dt3_nowrf Usp N :=
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]); try contradiction;
  subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
  clear - Hr N; unfold dt3_wfr in N; lia.

Lemma dt3_bufnot : forall ly1 S1 (W1 : world SEGS) m1 md1 cx e1 h1 ocap out1,
AR SEGS B ly1 S1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx) ->
re_cap e1 <> 0 ->
~ In (re_buf e1, re_cap e1) (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
  asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx).
Proof.
intros ly1 S1 W1 m1 md1 cx e1 h1 ocap out1 HAR HP Hc0.
pose proof (Permutation_NoDup HP (dt3_ablocks_nodup _ _ _ _ _ HAR)) as HND.
unfold aentry_blks in HND. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) Hc0) in HND. cbn [app] in HND.
apply List.NoDup_cons_iff in HND as [_ HND]. apply List.NoDup_cons_iff in HND as [Hbufnot _].
exact Hbufnot.
Qed.

Lemma dt3_pend_ne : forall ly1 S1 (W1 : world SEGS) m1 md1 cx e1 h1 ocap out1 b,
AR SEGS B ly1 S1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx) ->
re_cap e1 <> 0 -> In b (alist_blks (hs_pending h1)) -> b <> (re_buf e1, re_cap e1).
Proof.
intros ly1 S1 W1 m1 md1 cx e1 h1 ocap out1 b HAR HP Hc0 Hb X. subst b.
apply (dt3_bufnot ly1 S1 W1 m1 md1 cx e1 h1 ocap out1 HAR HP Hc0).
apply in_or_app; right. apply in_or_app; left. unfold asrc_blks. right. apply in_or_app; left. exact Hb.
Qed.

Lemma dt3_buf_awr : forall cx ly1 S1 (W1 : world SEGS) m1 md1 e1 h1 ocap out1 a,
AR SEGS B ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx) ->
re_cap e1 <> 0 -> re_cap e1 <> ATABLE -> In (re_buf e1, re_cap e1) (ablocks B ly1 S1) ->
re_buf e1 <= a < re_buf e1 + re_cap e1 ->
awr_byte DRAIN_STK (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) ly1 [] a.
Proof.
intros cx ly1 S1 W1 m1 md1 e1 h1 ocap out1 a HAR HP0 HP1 Hc0 HcT Hbin Ha.
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
pose proof (dt3_bufnot ly1 S1 W1 m1 md1 cx e1 h1 ocap out1 HAR HP1 Hc0) as Hbufnot.
assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
- right. left. split.
  + apply (Permutation_in _ HP0) in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|Hin0];
      [injection X as X1 X2; exfalso; apply HcT; symmetry; exact X2|].
    assert (Hin3 : In (re_buf e1, re_cap e1)
      (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
    { apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
      apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
      apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; right; exact X|].
      exfalso. apply Hbufnot. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
      exact Hin0. }
    unfold dFP, dr_fp. apply inFP_cons. right. exists (re_buf e1, re_buf e1 + req_size (re_cap e1)).
    split; [unfold ablocks_fp; exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ Hin3)|].
    cbn [fst snd]. rewrite RQC. lia.
  + exists (re_buf e1), (re_cap e1). split; [exact Hbin | rewrite RQC; lia].
- right. right. left. exists (re_buf e1), (re_cap e1). split; [exact Hbin|].
  split; [exact Hnot0 | rewrite RQC; lia].
Qed.

Definition dt3_hide (P : Prop) : Prop := P.

Lemma dt3_U_sub : forall E (a b : nat) x y, bv_unsigned (ew E a) = x -> bv_unsigned (ew E b) = y ->
0 <= y <= x ->
U E (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff b 0) (SLit (-1)))) = x - y.
Proof.
intros E a b x y Ha Hb Hxy.
pose proof (bv_unsigned_in_range 64 (ew E a)) as Ra. change (bv_modulus 64) with (2 ^ 64) in Ra. rewrite Ha in Ra.
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, Ha, Hb, !Z.add_0_r. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l, (Z.mod_small y) by lia.
change (-1 mod 2 ^ 64) with (2 ^ 64 - 1).
replace (x + y * (2 ^ 64 - 1)) with ((x - y) + y * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma dt3_data : forall cx sg D W1 c1,
DBASE B MT MMAX RG cx -> DT2 B MT MMAX RG cx sg D W1 c1 ->
drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg <> [] ->
(forall W2 c2, DRB B MT MMAX RG cx sg D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx sg D W1 c1 HB HT2 Hei Hpne Krb.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
destruct HT2 as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & HR & R23 & R19 & R10 & R13 & HMEM & HnoNUL & Hused & Hinb & HLINK & HSAME & HHIST & HJ1 & Hroom &
  Hlater & Hbud).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HR as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HB as (Hafn & HB10 & HBG & HGSA & HSAG & HSA8 & HBgarr & HBawr & HBeok & Hj4 & HBsrc & HBoth & HBfd &
  HBsk & HBsk0 & HBout & HBrom & HPERM0 & HBps & HBcap & HBnh & HBtr & HBbb & HBmo).
clear HB10 HBG HSA8 HBgarr HBawr HBeok HBsrc HBoth HBfd HBsk HBsk0 HBout HBrom HBps HBcap HBnh HBtr HBbb HBmo.
pose proof Hafn as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HspA : alloc_ceiling + DRAIN_STK <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HGin1) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAhi : dxSA cx + AENT <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof Hsrc as (V0 & V4 & V8 & V12 & HAWS & Hcl01 & Hei01 & Hopen & Hfdr & HPEND & V32 & V40 & V48 & V56 &
  Hrecs & Hnpart & Hovl & Hpin & Hpjl & Hpg & HnoW & HEXP & HHELD & HNDB).
pose proof HPEND as (P0 & P8 & P12 & PAW & Pn & Pv & PND & Pnv & Precs).
pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
  HND1 & HND2 & Hkeys).
assert (Hei0 : hs_eintr h1 = 0) by (rewrite Lei, Hei; reflexivity).
rewrite Hei0 in V12.
clear Hcl01 Hei01 Hovl Heof Hskip Hheld.
destruct Hrecs as [(Hnil & _) | (r0 & rs0 & Erecs & Hoff0 & HoffL)].
{ exfalso. apply Hpne. rewrite <- Lpend, Hnil. reflexivity. }
set (v := hl_v (hs_pending h1)) in *. set (off := hs_off h1) in *.
set (p := fst r0). set (len := Z.of_nat (length (snd r0))).
set (room := re_cap e1 - re_used e1).
assert (Hn1 : 1 <= hl_n (hs_pending h1) <= 2 ^ 30).
{ split; [|lia]. unfold hl_n. rewrite Erecs. cbn [length]. lia. }
destruct Pv as [(Hcap0 & _) | (Hcpv & Hvin & Hjv & Hvg)]; [exfalso; lia|].
rewrite Erecs in Hvg.
pose proof Precs as Precs'. rewrite Forall_forall in Precs'.
destruct (Precs' r0 ltac:(rewrite Erecs; left; reflexivity)) as (Hr0in & Hr0g & _ & Hr0len).
specialize (Hr0len eq_refl). clear Precs'.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hr0in) as (_ & Hs4096 & Hsceil & _).
pose proof (req_size_pos (len + 1) ltac:(lia)) as (_ & Rq0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hvin) as (_ & Hv4096 & Hvceil & Hvapp & _).
pose proof (req_size_pos (AREC * hl_cap (hs_pending h1)) ltac:(unfold AREC; lia)) as (_ & Rqv).
assert (Hpb : 4096 <= p <= 140737479966720) by (unfold p; unfold len in *; lia).
assert (Hlb : 1 <= len <= 2 ^ 47) by (unfold len in *; lia).
assert (Hob : 0 <= off < len) by (unfold off, len in *; lia).
assert (Hul : ulen sg = re_used e1) by (unfold ulen; rewrite <- Lu; unfold bzs; rewrite length_map; exact HUlen).
assert (Hroom2 : 4096 <= room).
{ unfold room. rewrite <- Hul. rewrite <- Lcap in Hroom. exact Hroom. }
assert (Hcapb : re_cap e1 <= 16384) by lia.
assert (Hroomb : 0 < room <= 16384) by (unfold room; lia).
clear Hcapr.
unfold room in Hroom2.
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [exfalso; lia|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in Hbceil.
assert (Hpend0 : drain_b_c.ds_pend sg = bzs (snd r0) :: map (fun r => bzs (snd r)) rs0)
  by (rewrite <- Lpend, Erecs; reflexivity).
assert (Hdhead : dhead sg = bzs (snd r0)) by (unfold dhead; rewrite Hpend0; reflexivity).
assert (Hdn : dnum sg = Z.min (len - off) room).
{ unfold dnum. rewrite Hdhead. unfold bzs. rewrite length_map. rewrite <- Loff, <- Lcap, Hul.
  unfold len, off, room. reflexivity. }
set (dn := dnum sg) in *.
assert (Hdnr : 1 <= dn <= 16384) by (rewrite Hdn; lia).
assert (Hdnl : dn <= len - off) by (rewrite Hdn; lia).
assert (Hdnc : dn <= room) by (rewrite Hdn; lia).
assert (Hdnh : dt3_hide (dn = Z.min (len - off) room)) by exact Hdn.
clear Hdn.
assert (Hmod8 : p mod 8 = 0).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hr0in) as (H16 & _).
  apply Z.mod_divide in H16; [|lia]. destruct H16 as (q & Hq). unfold p. rewrite Hq.
  replace (q * 16) with (0 + (2 * q) * 8) by lia. apply dt3_mod_addk; [lia | reflexivity]. }
destruct (dt3_rec_vm (arm W1 m1) v r0 rs0 _ Hvg ltac:(unfold p in Hpb; lia) ltac:(unfold len in *; lia))
  as (VP & VL).
assert (V16 : val_mem SEGS (arm W1 m1) (dHA RG cx + 16) 8 v) by exact P0.
assert (V24 : val_mem SEGS (arm W1 m1) (dHA RG cx + 24) 4 (hl_n (hs_pending h1)))
  by (replace (dHA RG cx + 24) with (dHA RG cx + 16 + 8) by lia; exact P8).
assert (HW : forall o, 0 <= o < DRAIN_FRAME -> writable_at SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o))
  by (intros o Hoo; exact (dtm_frame_wr B RG HGSB cx ly1 S1 W1 m1 md1 k1 o HJ Hoo)).
assert (HvG : v + 16 <= rg_s RG \/ rg_s RG + 4 * ASRC <= v).
{ destruct (Z_lt_le_dec (v + 15) (rg_s RG)) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_le_dec v (rg_s RG + 4 * ASRC)) as [Hlt2|Hge2]; [|right; lia].
  exfalso. destruct (Z_lt_le_dec v (rg_s RG)) as [Hlt3|Hge3].
  - destruct (dtk_blk_off B RG LAWS HGSB ly1 S1 W1 m1 md1 v (AREC * hl_cap (hs_pending h1)) (rg_s RG) HAR Hvin
      ltac:(unfold AREC in *; lia)) as (_ & Hno). apply Hno. unfold ASRC; lia.
  - destruct (dtk_blk_off B RG LAWS HGSB ly1 S1 W1 m1 md1 v (AREC * hl_cap (hs_pending h1)) v HAR Hvin
      ltac:(unfold AREC in *; lia)) as (_ & Hno). apply Hno. lia. }
assert (Hv3 : v mod 8 = 0).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hvin) as (H16 & _).
  apply Z.mod_divide in H16; [|lia]. destruct H16 as (q & Hq). rewrite Hq.
  replace (q * 16) with (0 + (2 * q) * 8) by lia. apply dt3_mod_addk; [lia | reflexivity]. }
pose proof (dt3_seat1 cx W1 m1 regs1 (hl_n (hs_pending h1)) v len off p dn HR R23 Hj4 HSAlo HSAhi HspA HspB HspM
  HFR HW ltac:(lia) ltac:(lia) ltac:(unfold AREC in *; lia) Hv3 HvG Hlb ltac:(lia) Hpb Hmod8 Hdnr
  V12 V16 V24 V32 VP VL) as HS.
clear HvG.
remember (Eimg (Ereg regs1 (dt3_x1 (hl_n (hs_pending h1)) v len off p dn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (k : nat) (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ k r Hr)).
assert (EX : forall i, (i < 7)%nat ->
    ew E (32 + i) = nth i (dt3_x1 (hl_n (hs_pending h1)) v len off p dn) (Z_to_bv 64 0))
  by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ i)).
clear HE.
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E10 : ew E 10 = Z_to_bv 64 (re_buf e1 + re_used e1))
  by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact R10).
assert (E13 : ew E 13 = Z_to_bv 64 room) by (rewrite (EREG 13%nat 13%bv) by (first [lia | reflexivity]); exact R13).
assert (E19 : ew E 19 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 (dxSA cx)) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E23 : ew E 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 v) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 off) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 p) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 dn) by exact (EX 6%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (HHA : dHA RG cx = rg_s RG + 96 * Z.of_nat (dxj cx)) by (unfold dHA, ASRC; reflexivity).
assert (HAb : 0 <= dHA RG cx /\ dHA RG cx + 96 < 2 ^ 47) by (rewrite HHA; unfold IMG_TOP, ASRC in *; lia).
assert (UB2 : U E dts_Bx2 = SHADOW_OFF) by (unfold dts_Bx2; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; unfold AREC in *; lia).
assert (SHA : forall E' mem md, ew E' 23 = Z_to_bv 64 (dHA RG cx) -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  ew E' 34 = Z_to_bv 64 v -> AR SEGS B ly1 S1 W1 mem md -> sh_ok SEGS dts_Bx2 dt3_SH E' (mrestrict (w_H W1) mem)).
{ intros E' mem md F23 F32 F34 HARm. unfold sh_ok, dt3_SH.
  assert (UB2' : U E' dts_Bx2 = SHADOW_OFF) by (unfold dts_Bx2; apply U_atom; [exact F32 | unfold SHADOW_OFF; lia]).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range SEGS (w_H W1) mem E' dts_Bx2 23%nat (rg_s RG) (4 * ASRC) (dHA RG cx) 0 96).
    + exact (azs_range_addressable B LAWS ly1 S1 W1 mem md (rg_s RG) (4 * ASRC) HARm HGSZ).
    + exact UB2'.
    + apply (U_atom E' 23 (dHA RG cx) F23). lia.
    + rewrite HHA; lia.
    + rewrite HHA; unfold ASRC in *; lia.
    + intros x Hx. rewrite HHA in Hx. unfold SHADOW_OFF, IMG_TOP, ASRC in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W1) mem E' dts_Bx2 34%nat v (AREC * hl_cap (hs_pending h1)) v 0 16).
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mem md v (AREC * hl_cap (hs_pending h1)) v
        (AREC * hl_cap (hs_pending h1)) HARm Hvin); [lia | lia].
    + exact UB2'.
    + apply (U_atom E' 34 v F34). unfold AREC in *; lia.
    + lia.
    + unfold AREC in *; lia.
    + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by (unfold AREC in *; lia).
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AREC in *. lia. }
pose proof (SHA E m1 md1 E23 E32 E34 HAR) as SHOK.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
paj_run_to_tok RUNTO HS HJ SHOK dts_Bspan dt3_sh1; [dt3_awr Usp |].
rename HFr into FR1; rename HG0 into GR1; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msA end.
dt3_rs HS E HHA E8 E19 E23 E32 cx (12%bv : bv 5) 12.
paj_run_to_tok RUNTO HS HJ SHOK dts_Bspan dt3_sh2; [dt3_awr Usp |].
rename HFr into FR2; rename HG0 into GR2; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
dt3_rs HS E HHA E8 E19 E23 E32 cx (11%bv : bv 5) 24.
paj_run_to_tok RUNTO HS HJ SHOK dts_Bspan dt3_sh3; [dt3_awr Usp |].
rename HFr into FR3; rename HG0 into GR3; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msC end.
dt3_rs HS E HHA E8 E19 E23 E32 cx (11%bv : bv 5) 16.
paj_run_to_tok RUNTO HS HJ SHOK dts_Bspan dt3_sh4; [dt3_awr Usp |].
rename HFr into FR4; rename HG0 into GR4; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msD end.
dt3_rs HS E HHA E8 E19 E23 E32 cx (14%bv : bv 5) 32.
paj_run_tok RUN HS HJ SHOK dts_Bspan; [dt3_awr Usp |].
rename HFr into FR5; rename HG0 into GR5; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msE end.
assert (KALLE : forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x ->
  aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N.
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msD) (ms_mem msE) FR5 x Hx) by (dt3_nowrf Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msC) (ms_mem msD) FR4 x Hx) by (dt3_nowrf Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msB) (ms_mem msC) FR3 x Hx) by (dt3_nowrf Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msA) (ms_mem msB) FR2 x Hx) by (dt3_nowrf Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) m1 (ms_mem msA) FR1 x Hx) by (dt3_nowrf Usp N).
  reflexivity. }
assert (PRESE : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msE) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR5 (apresent_grows _ _ _ _ GR4
      (apresent_grows _ _ _ _ GR3 (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hp)))))).
assert (E13u : bv_unsigned (ew E 13) = room) by (rewrite E13; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = len) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = off) by (rewrite E36; apply unsigned_lit_small; lia).
assert (USUB : U E (SAlu ALU_ADD (SOff 35 0) (SMd M_MUL (SOff 36 0) (SLit (-1)))) = len - off)
  by (apply (dt3_U_sub E 35 36 len off E35u E36u); lia).
assert (UPV : U E (SOff 37 0) = p) by (apply U_atom; [exact E37 | lia]).
assert (UOF : U E (SOff 36 0) = off) by (apply U_atom; [exact E36 | lia]).
assert (UP0 : U E (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) = off + p)
  by (apply (trap_U_add E (SOff 36 0) (SOff 37 0) off p UOF UPV); lia).
assert (TR1 : branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)))
  (sv_denot E (SOff 37 0)) = false)
  by (apply (trap_ptr_bltu E (SOff 37 0) (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) p (off + p) UPV UP0); lia).
eassert (CONT : forall (msF : machine_state) (mdF : Model),
  st_ok_pi SEGS VAL E ?[SSF] (restrict (w_H W1) msF) ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
    (dxmd cx) [] ly1 S1 W1 (ms_mem msF) mdF k1 ->
  sh_ok SEGS dts_Bx2 dt3_SH E (mrestrict (w_H W1) (ms_mem msF)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x -> aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x) ->
  (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x) ->
  SRr SEGS W1 (mkCfg msF mdF) (dPOST B MT RG cx)).
2: {
psrr_branch_tok RUN BR HS SHOK dts_Bspan;
[ rewrite trap_br_ltu, USUB, (U_atom E 13 room E13 ltac:(lia)) in Hc; apply Z.ltb_lt in Hc;
  assert (Hdn2 : dn = len - off) by (clear - Hc Hdnh; unfold dt3_hide in Hdnh; lia);
  paj_run_to_tok RUNTO HS HJ SHOK dts_Bspan dt3_pc_n; [dt3_awr Usp |];
  rename HFr into FR6; rename HG0 into GR6; clear HF;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    dt3_reg HS (12%bv : bv 5) X12;
    assert (D12 : sv_denot E (SOff 38 0) = getr (ms_regs mx) 12%bv)
      by (rewrite X12, (den_atom0 E 38 dn E38) by lia;
          rewrite denot_lit_U, USUB, Hdn2; reflexivity) end
| rewrite trap_br_ltu, USUB, (U_atom E 13 room E13 ltac:(lia)) in Hc; apply Z.ltb_ge in Hc;
  assert (Hdn2 : dn = room) by (clear - Hc Hdnh; unfold dt3_hide in Hdnh; lia);
  paj_run_to_tok RUNTO HS HJ SHOK dts_Bspan dt3_pc_n; [dt3_awr Usp |];
  rename HFr into FR6; rename HG0 into GR6; clear HF;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    dt3_reg HS (12%bv : bv 5) X12;
    assert (D12 : sv_denot E (SOff 38 0) = getr (ms_regs mx) 12%bv)
      by (rewrite X12, (den_atom0 E 13 room E13) by lia; rewrite (den_atom0 E 38 dn E38) by lia;
          rewrite Hdn2; reflexivity) end ].
all: clear Hc Hdn2.
all: match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
all: pose proof (ast_ok_pi_set_reg_fp E _ _ (12%bv : bv 5) _ HS eq_refl D12) as HS';
     clear HS D12 X12; rename HS' into HS;
     cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
all: pose proof (st_ok_pi_facts_incl E _ _ _ _ HS (fun x Hx => Hx) (fun x Hx => Hx)) as HS'; clear HS;
     rename HS' into HS.
all: match type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
all: apply (CONT msF _ HS HJ SHOK);
  [ intros x Hx N; rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msE) (ms_mem msF) FR6 x Hx) by (dt3_nowrf Usp N);
    exact (KALLE x Hx N)
  | intros x Hp; exact (apresent_grows _ _ _ _ GR6 (PRESE x Hp)) ]. }
intros msF mdF HSc HJc SHc KALLF PRESF.
clear HS HJ SHOK KALLE PRESE FR1 FR2 FR3 FR4 FR5 GR1 GR2 GR3 GR4 GR5.
rename HSc into HS, HJc into HJ, SHc into SHOK.
paj_run_tok RUN HS HJ SHOK dts_Bspan; [dt3_awr Usp |].
rename HFr into FR7; rename HG0 into GR7; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msG end.
psrr_branch_tok RUN BR HS SHOK dts_Bspan; try (dt3_trap Hc TR1).
clear Hc.
paj_run_tok RUN HS HJ SHOK dts_Bspan; [dt3_awr Usp |].
rename HFr into FR8; rename HG0 into GR8; clear HF.
match type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into msM end.
assert (KALLM : forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x ->
  aview SEGS (w_H W1) (ms_mem msM) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N.
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msG) (ms_mem msM) FR8 x Hx) by (dt3_nowrf Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msF) (ms_mem msG) FR7 x Hx) by (dt3_nowrf Usp N).
  exact (KALLF x Hx N). }
assert (PRESM : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msM) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR8 (apresent_grows _ _ _ _ GR7 (PRESF x Hp)))).
clear FR7 FR8 GR7 GR8 KALLF PRESF.
subst dn room len p off v.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. dt3_reg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp2 : spZ (ms_regs msM) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Usp).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARM.
assert (Hbne : re_cap e1 <> 0) by lia.
assert (Hrin : In (fst r0, Z.of_nat (length (snd r0)) + 1) (alist_blks (hs_pending h1))).
{ unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbn [app]. right. rewrite Erecs. cbn [map]. left.
  reflexivity. }
assert (Hvinl : In (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1)) (alist_blks (hs_pending h1))).
{ unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbn [app]. left. reflexivity. }
pose proof (dt3_blk_apart _ _ _ _ _ _ _ _ _ HAR Hr0in Hbin
  (dt3_pend_ne ly1 S1 W1 m1 md1 cx e1 h1 _ out1 _ HAR Hperm Hbne Hrin)) as Htap. rewrite RQC in Htap.
pose proof (dt3_blk_apart _ _ _ _ _ _ _ _ _ HAR Hvin Hbin
  (dt3_pend_ne ly1 S1 W1 m1 md1 cx e1 h1 _ out1 _ HAR Hperm Hbne Hvinl)) as Hvap. rewrite RQC in Hvap.
pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR Hbin) as Hboff. rewrite RQC in Hboff.
destruct HJ as (HSTK2 & HXO2 & (memS2 & HJi2 & HAG2) & HOUT2). rewrite !Z.add_0_r in HJi2.
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA WS_asan_memcpy) AMEMCPY W1 (ms_regs msM) (ms_mem msM)
    DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS2 (dxmd cx) [] ly1 S1 _ k1
    (re_buf e1 + re_used e1) (hs_off h1 + fst r0) (dnum sg) (- DRAIN_FRAME) _ HJi2);
  [ rewrite Q10, E10; reflexivity
  | rewrite Q11, denot_lit_U, UP0; reflexivity
  | rewrite Q12, E38; reflexivity
  | clear - Hdnr; lia
  | clear - Hb4096 HUlen; lia
  | clear - Hbceil Hdnc HUlen C1; lia
  | rewrite Usp2; ring
  | rewrite HDF; reflexivity
  | rewrite HDF; lia
  | rewrite HDS, HDF; unfold ESTACK; lia
  | rewrite Q3, (EREG 3%nat 3%bv), R3 by (first [lia | reflexivity]); exact Hgp0
  | rewrite Q4, (EREG 4%nat 4%bv), R4 by (first [lia | reflexivity]); exact Htp0
  | exact Q1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; split;
    [ apply (dt3_buf_awr cx ly1 S1 W1 m1 md1 e1 h1 _ out1 a HAR HPERM0 Hperm Hbne);
        [ unfold ATABLE; clear - Hroom2 HUlen; lia | exact Hbin | clear - Ha Hdnc HUlen; lia ]
    | clear - Ha Hbceil Hdnc HUlen HspA HDS HDF; unfold ESTACK; lia ]
  | apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1));
      [exact HAR | exact Hbin | clear - HUlen; lia | rewrite RQC; clear - Hdnc HUlen; lia]
  | eapply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (re_buf e1) (re_cap e1));
      [exact HARM | exact Hbin | clear - HUlen; lia | rewrite RQC; clear - Hdnc HUlen; lia]
  | intros Hpos; eapply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (re_buf e1) (re_cap e1));
      [exact HARM | exact Hbin | clear - HUlen; lia | rewrite RQC; clear - Hdnc HUlen; lia | exact Hpos]
  | split; [clear - Hoff0 Hs4096; lia|];
    split; [clear - Hsceil Hdnl HoffL Hoff0 Rq0 C1; lia|];
    split; [|split; [clear - Htap Hdnl Hdnc Hoff0 HoffL HUlen Rq0 Hdnr; unfold dt3_apart in Htap; lia|]];
    [ intros a Ha; split; [|rewrite Usp2; clear - Ha Hsceil Hdnl Hoff0 HoffL Rq0 HspA HDS HDF; unfold ESTACK; lia];
      rewrite KALLM by (clear - Ha Hsceil Hdnl Hoff0 HoffL Hs4096 Rq0 HspA HDS HDF C1; unfold dt3_wfr; lia);
      replace a with (fst r0 + Z.of_nat (Z.to_nat (a - fst r0))) by (clear - Ha Hoff0; lia);
      rewrite (dt3_garr8_aview W1 m1 _ _ _ Hr0g)
        by (rewrite dt3_bzs_len, length_app; cbn [length]; clear - Ha HoffL Hdnl Hoff0; lia);
      discriminate
    | split; [apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (fst r0) (Z.of_nat (length (snd r0)) + 1));
        [exact HAR | exact Hr0in | clear - Hoff0; lia | clear - Hdnl HoffL Hoff0 Rq0; lia]|];
      split; [eapply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (fst r0)
        (Z.of_nat (length (snd r0)) + 1)); [exact HARM | exact Hr0in | clear - Hoff0; lia
        | clear - Hdnl HoffL Hoff0 Rq0; lia]|];
      intros Hpos; eapply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msM) _ (fst r0)
        (Z.of_nat (length (snd r0)) + 1)); [exact HARM | exact Hr0in | clear - Hoff0; lia
        | clear - Hdnl HoffL Hoff0 Rq0; lia | exact Hpos] ] ]
| ].
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3i & HP3 & Hd10b & Hcpy & Hfr3 & Hpres3).
jafter_call_keep_pi HS 39%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  all: first
    [ apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3];
      intros a Ha; apply Hfr3; clear - Ha Hbceil Hdnc HUlen HspA HspB HDS HDF C1; unfold ESTACK; lia
    | apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 23 (dHA RG cx)); [exact U23 | | exact Hpres3];
      intros a Ha; apply Hfr3; clear - Ha HAb Hboff Hdnc HUlen HspA HDS HDF HHA G1 G2 C1 Hj4;
      unfold YCbq.off_img, ESTACK, ASRC, IMG_TOP in *; lia
    | apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 34 (hl_v (hs_pending h1))); [exact U34 | | exact Hpres3];
      intros a Ha; apply Hfr3; clear - Ha Hvap Hv4096 Hvceil Rqv Hcpv Hdnc HUlen HspA HDS HDF C1;
      unfold dt3_apart, AREC, ESTACK in *; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 39 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 39)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDa by lia; exact Usp).
pose proof (proj1 HJ3i) as HAR3.
assert (SHOK3 : sh_ok SEGS dts_Bx2 dt3_SH Ea (mrestrict (w_H W1) mem3))
  by (apply (SHA Ea mem3 md3); [rewrite OLDa by lia; exact E23 | rewrite OLDa by lia; exact E32
      | rewrite OLDa by lia; exact E34 | exact HAR3]).
assert (HJ3 : @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
  (dxmem cx) (dxmd cx) [] ly1 S1 W1 mem3 md3 k1)
  by (apply (ajournal_gx_pack SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
    (dxmem cx) (dxmd cx) [] ly1 S1 W1 mem3 md3 k1 memS2);
    [exact HSTK2 | lia | rewrite !Z.add_0_r; exact HJ3i | exact HAG2 | apply out_none]).
clear HJ3i HAG2 HOUT2.
assert (A36 : U Ea (SOff 36 0) = hs_off h1) by (apply U_atom; [rewrite OLDa by lia; exact E36 | lia]).
assert (A37 : U Ea (SOff 37 0) = fst r0) by (apply U_atom; [rewrite OLDa by lia; exact E37 | lia]).
paj_run_to_tok RUNTO HS HJ3 SHOK3 dts_Bspan dt3_pc_drb; [dt3_awr UspA |].
rename HFr into FR10; rename HG0 into GR10; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msR end.
assert (K10 : forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x ->
  aview SEGS (w_H W1) (ms_mem msR) x = aview SEGS (w_H W1) mem3 x).
{ intros x Hx N. rewrite (aview_kept_out _ _ (w_H W1) mem3 (ms_mem msR) FR10 x Hx) by (dt3_nowrf UspA N).
  reflexivity. }
assert (PRESR : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msR) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR10 (Hpres3 _ (PRESM x Hp)))).
set (data := firstn (Z.to_nat (dnum sg)) (skipn (Z.to_nat (hs_off h1)) (snd r0))).
assert (Hdlen : length data = Z.to_nat (dnum sg))
  by (unfold data; rewrite length_firstn, length_skipn; clear - Hdnl Hoff0 HoffL Hdnr; lia).
assert (Hdlj : (length data <= length (re_junk e1))%nat) by (rewrite Hdlen; clear - Hjl Hdnc Hdnr; lia).
assert (CPY : forall i, (i < length data)%nat ->
  aview SEGS (w_H W1) (ms_mem msR) (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)).
{ intros i Hi. rewrite Hdlen in Hi.
  assert (Hi' : 0 <= Z.of_nat i < dnum sg) by (clear - Hi Hdnr; lia).
  rewrite K10 by (clear - Hi' Hb4096 Hbceil Hdnc HUlen HspA HDS HDF C1; unfold dt3_wfr; lia).
  pose proof (Hcpy (Z.of_nat i) Hi') as Hc. cbv iota in Hc. rewrite Hc.
  rewrite KALLM by (clear - Hi' Hsceil Hdnl Hoff0 HoffL Hs4096 Rq0 HspA HDS HDF C1; unfold dt3_wfr; lia).
  replace (hs_off h1 + fst r0 + Z.of_nat i) with (fst r0 + Z.of_nat (Z.to_nat (hs_off h1) + i))
    by (clear - Hoff0; lia).
  rewrite (dt3_garr8_aview W1 m1 _ _ _ Hr0g)
    by (rewrite dt3_bzs_len, length_app; cbn [length]; clear - Hi HoffL Hdnl Hoff0 Hdnr; lia).
  f_equal. unfold data. apply dt3_nth_data; clear - Hi HoffL Hdnl Hoff0 Hdnr; lia. }
assert (KEEP : forall x, 0 <= x < 2 ^ 64 ->
  ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
  ~ (dsp0 cx - DRAIN_STK <= x < dsp0 cx) ->
  aview SEGS (w_H W1) (ms_mem msR) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. rewrite Hdlen in N1.
  assert (NW : ~ dt3_wfr cx x) by (clear - N2 HDS HDF; unfold dt3_wfr; lia).
  rewrite (K10 x Hx NW).
  rewrite (Hfr3 x Hx ltac:(clear - N1 Hdnr; lia) ltac:(clear - N2 HDS HDF; unfold ESTACK; lia)).
  exact (KALLM x Hx NW). }
assert (HFRR : dr_frame RG cx W1 (ms_mem msR)).
{ apply (dt3_frame_kept cx W1 m1 (ms_mem msR) HFR HspA HspB).
  intros x Hx N. assert (Hx64 : 0 <= x < 2 ^ 64) by (clear - Hx HspA HspB HDS HDF C1; lia).
  rewrite (K10 x Hx64 N).
  rewrite (Hfr3 x Hx64 ltac:(clear - Hx Hbceil Hdnc HUlen HspA HDS HDF; lia)
    ltac:(clear - Hx HDF; unfold ESTACK; lia)).
  exact (KALLM x Hx64 N). }
pose proof (dt3_dmem_drb cx sg ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 (ms_mem msR) _ data
  HB HMEM HJ3 Hcpos Hdlj KEEP PRESR CPY HFRR) as HMEMF.
assert (Hstr : dstrict sg).
{ intros r rs Hrs. rewrite Hpend0 in Hrs. injection Hrs as <- _. rewrite dt3_bzs_len, <- Loff. clear - HoffL. lia. }
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS24. cbn [ms_mem restrict] in RS24.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS96. cbn [ms_mem restrict] in RS96.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS112. cbn [ms_mem restrict] in RS112.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS160. cbn [ms_mem restrict] in RS160.
pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RS168. cbn [ms_mem restrict] in RS168.
pose proof (st_ok_pi_region_nth _ _ _ 5 _ HS eq_refl) as RS192. cbn [ms_mem restrict] in RS192.
assert (F8 : ew Ea 8 = Z_to_bv 64 (rg_s RG)) by (rewrite OLDa by lia; exact E8).
assert (F19 : ew Ea 19 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx))) by (rewrite OLDa by lia; exact E19).
assert (F23 : ew Ea 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite OLDa by lia; exact E23).
assert (F23g : ew Ea 23 = Z_to_bv 64 (rg_s RG + 96 * Z.of_nat (dxj cx))) by (rewrite <- HHA; exact F23).
assert (F32 : ew Ea 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; exact E32).
assert (F37 : ew Ea 37 = Z_to_bv 64 (fst r0)) by (rewrite OLDa by lia; exact E37).
assert (F38 : ew Ea 38 = Z_to_bv 64 (dnum sg)) by (rewrite OLDa by lia; exact E38).
assert (UP0a : U Ea (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) = hs_off h1 + fst r0)
  by (apply (trap_U_add Ea (SOff 36 0) (SOff 37 0) (hs_off h1) (fst r0) A36 A37); lia).
assert (R64 : forall z, 0 <= z < 2 ^ 64 -> 0 <= z < 2 ^ (8 * Z.of_N 8)) by (intros z Hz; exact Hz).
assert (V24F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 24) 8 (dHA RG cx + 56)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 32 24 32 24 8%N (SOff 23 56) (dHA RG cx + 56)
      RS24 UspA);
    [left; reflexivity | apply (den_atom Ea 23 (dHA RG cx) 56 F23); lia | apply R64; lia | lia]. }
assert (V96F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 96) 8 (dHA RG cx + 16)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 96 104 96 104 96 8%N (SOff 23 16) (dHA RG cx + 16)
      RS96 UspA);
    [left; reflexivity | apply (den_atom Ea 23 (dHA RG cx) 16 F23); lia | apply R64; lia | lia]. }
assert (V160F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 160) 8 (dHA RG cx + 64)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 160 168 160 168 160 8%N (SOff 23 64) (dHA RG cx + 64)
      RS160 UspA);
    [left; reflexivity | apply (den_atom Ea 23 (dHA RG cx) 64 F23); lia | apply R64; lia | lia]. }
assert (V112F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 112) 8 (shadow_addr (dHA RG cx + 16))).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 112 120 112 120 112 8%N
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 16) (SLit 3)) (SOff 32 0)) (shadow_addr (dHA RG cx + 16))
      RS112 UspA);
    [left; reflexivity | apply (dt3_den_shA Ea 23 (dHA RG cx) 16 F23 F32); lia | apply R64, dt3_sh_range; lia | lia]. }
assert (V168F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 168) 8 (shadow_addr (dHA RG cx + 32))).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 168 176 168 176 168 8%N
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 32) (SLit 3)) (SOff 32 0)) (shadow_addr (dHA RG cx + 32))
      RS168 UspA);
    [left; reflexivity | apply (dt3_den_shA Ea 23 (dHA RG cx) 32 F23 F32); lia | apply R64, dt3_sh_range; lia | lia]. }
assert (V192F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 192) 8 (dnum sg)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 192 200 192 200 192 8%N (SOff 38 0) (dnum sg)
      RS192 UspA);
    [left; reflexivity | apply (den_atom0 Ea 38 (dnum sg) F38); lia | apply R64; lia | lia]. }
clear RS24 RS96 RS112 RS160 RS168 RS192.
pmkst HS.
prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3. prreg HS (4%bv : bv 5) Y4.
prreg HS (8%bv : bv 5) Y8. prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18. prreg HS (23%bv : bv 5) Y23.
prreg HS (15%bv : bv 5) Y15. prreg HS (21%bv : bv 5) Y21. prreg HS (6%bv : bv 5) Y6. prreg HS (20%bv : bv 5) Y20.
dt3_reg HS (27%bv : bv 5) Y27. dt3_reg HS (19%bv : bv 5) Y19. dt3_reg HS (24%bv : bv 5) Y24.
dt3_reg HS (16%bv : bv 5) Y16. dt3_reg HS (17%bv : bv 5) Y17. dt3_reg HS (22%bv : bv 5) Y22.
rewrite ?OLDa in Y2, Y3, Y4, Y8, Y9, Y18, Y23, Y15, Y21, Y6 by lia.
assert (RP0 : forall r : bv 5, getr (ms_regs msR) r = sv_denot Ea (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) ->
  getr (ms_regs msR) r = w64 (fst r0 + drain_b_c.ds_off sg + Z.of_nat 0)).
{ intros r Hr. rewrite Hr, denot_lit_U, UP0a. unfold w64. f_equal. rewrite <- Loff. lia. }
assert (RSH : forall (r : bv 5) c, 0 <= c <= 56 ->
  getr (ms_regs msR) r = sv_denot Ea (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 c) (SLit 3)) (SOff 19 0)) ->
  getr (ms_regs msR) r = w64 (shadow_addr (dHA RG cx + c))).
{ intros r c Hc Hr. rewrite Hr.
  rewrite (dt3_den_resh Ea (rg_s RG) (Z.of_nat (dxj cx)) c F8 F19 F23g F32) by (try rewrite <- HHA; lia).
  exact (dt3_den_shA Ea 23 (dHA RG cx) c F23 F32 ltac:(lia) ltac:(lia)). }
match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdR := mdx) in * end.
apply (Krb W1). unfold DRB.
exists (ms_regs msR), ly1, S1, (ms_mem msR), mdR, k1, (dt3_junk e1 (data ++ skipn (length data) (re_junk e1))),
  h1, out1, ev1, LB1, spent, jb, aa, (drain_b_c.da_ev aa), (drain_b_c.da_erecs aa), tl,
  (fst r0 + drain_b_c.ds_off sg), r0, rs0.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ; rewrite Y2; exact Usp|].
split; [rewrite Y3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
split; [rewrite Y4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
split; [rewrite Y8; exact E8|].
split; [rewrite Y9, (EREG 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
split; [rewrite Y18, (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
split; [rewrite Y23; exact E23|].
split; [rewrite Y15; exact E38|].
split; [rewrite Y21, E38; change (Z.of_nat 0) with 0; rewrite Z.sub_0_r; reflexivity|].
split; [rewrite (RP0 _ Y27); change (Z.of_nat 0) with 0; rewrite Z.add_0_r; reflexivity|].
split; [exact (RP0 _ Y19)|].
split; [exact (RP0 _ Y24)|].
split; [rewrite Y6; exact E37|].
split; [rewrite Y20; reflexivity|].
split; [exact (RSH _ 40 ltac:(lia) Y16)|].
split; [exact (RSH _ 48 ltac:(lia) Y17)|].
split; [exact (RSH _ 56 ltac:(lia) Y22)|].
split; [exact HFRR|].
split; [exact V24F|]. split; [exact V96F|]. split; [exact V160F|].
split; [exact V112F|]. split; [exact V168F|]. split; [exact V192F|].
split; [exact Erecs|].
split; [reflexivity|].
split; [unfold dinband; clear - Hs4096 Hsceil Rq0 Hmod8 C1; unfold DCEIL; lia|].
split; [rewrite <- Loff; clear - Hoff0; lia|].
split; [clear - Hdnr; lia|].
split; [clear - Hdnr; lia|].
split.
{ cbn [dt3_junk re_junk].
  rewrite firstn_app, Hdlen, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite Hdlen; apply le_n).
  unfold data, ddata. rewrite Hdhead, <- Loff, dt3_skipn_bzs, dt3_firstn_bzs. reflexivity. }
split; [exact HMEMF|].
split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hinb|]. split; [exact HSAME|].
split; [exact Lcap|]. split; [exact Lu|]. split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|].
split; [exact Hei0|]. split; [exact Lpend|]. split; [exact Loff|].
split; [rewrite firstn_O, dtm_feed_nil; exact Lst|].
split; [rewrite firstn_O, dtm_lines_nil; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact Len|].
split; [rewrite firstn_O, dtm_lines_nil, dtm_pcapm_nil; exact Lecap|].
split; [rewrite firstn_O, app_nil_r; exact HHIST|].
split.
{ unfold RSTART. split; [exact (proj1 (proj2 HHIST))|]. split; [exact HJ1|]. split; [exact Hroom|].
  split; [exact Lwf|]. split; [exact Hstr|]. split; [exact Hei | exact Hpne]. }
split; [eapply dtm_pfut0; eassumption | exact Hbud].
Qed.


Theorem dr_toptail : dr_toptail_stmt B MT MMAX RG.
Proof.
intros cx sg D W1 c1 HB HDT KEI KEND KRB.
destruct (drain_b_c.ds_eintr sg) eqn:EI.
- exact (dt1_eintr cx sg D W1 c1 HB HDT EI (KEI eq_refl)).
- destruct (drain_b_c.ds_pend sg) as [|r0 rs0] eqn:EP.
  + exact (dt2_end cx sg D W1 c1 HB HDT EI EP KEND).
  + refine (dt3_data cx sg D W1 c1 HB HDT EI _ KRB). rewrite EP. discriminate.
Qed.

End c.
End b.
End a.

(* ---- THE GENERIC WALK (an internal work row, the ARx drain walk DR_x; the image-B twin of lib/A/W_drain_topb.v's generic Section
   c, a working branch ad3100d63f5).  dr_toptail_x : W_drain_topb_cx.v dr_toptail_stmt_x, over any
   allocator relation ARx with its laws, at the room parameter RP: the AR walk above (dt1_eintr / dt2_end / dt3_data
   and dr_toptail), copied with the AR forms converted to their _x forms (W_drain_cx_x.v Section c's hypotheses).
   The tail calls no allocator, so the cut's ghost list Hp1 and its dbud_x (room and counts at ly1 / S1 / tl) carry
   unchanged from DT2_x to DI_x / DEND_x / DRB_x; the two callees, __errno_location (AERRNO) and __asan_memcpy
   (AMEMCPY), keep the caller's allocator state and ghost list (W_sites_x.v aj_gx_entry_at_x / aj_intrin_at_x).
   HP0 serves the block shadow facts (W_journal_x.v's *_of_block_hp0_x), BLKN the size bound the block-apartness
   and no-duplicate lemmas read (AR's al_blocks carried it, alx_blocks does not).  No image-cover hypothesis: a live
   block's bytes are off the image by YCbqG.blk_img_x, and the walk's g_s / errno / output cells are image bytes by
   HG / HGO (dtk_low_img_x, dtk_blk_off_x, dt3_blk_gs_x and dtk_fp_out_x read the image so, where the AR text read
   the band 0x10000 .. IMG_TOP).  The stack width is W_contract_x.v's DRAIN_STK_x (DRAIN_STK + 128) in every
   journal, awr_byte and stack-window form, as DBASE_x and DMEM_x carry it; the AR lemmas cited that read the AR
   width DRAIN_STK get their premise from the larger one.  Every lemma above that reads no AR hypothesis is cited,
   not copied.  The AR text above is unchanged; it is compiled before the Requires below, so no name of the generic
   kit is in scope in it (W_drain_topb_cx.v, which it Requires, loads the kit without Importing it, and its own global
   zify line keeps the flag false). ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* the zify flag this file's AR text runs with (its own setting above), whatever the Requires above leave *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the shared Section texts (drx-a7: HP0 / BLKN): the ghost list of every ARx state is empty (the block shadow facts
   of W_journal_x.v's *_of_block_hp0_x), and a live block's size is non-negative (alx_blocks has no size conjunct) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

Lemma dts_shent_gs_x : forall ly1 S1 hp1 (W1 : world SEGS) m1 md1 E (j : nat),
ARx ly1 S1 hp1 W1 m1 md1 -> (j < 4)%nat ->
U E dts_Bx1 = SHADOW_OFF + 12 * Z.of_nat j -> U E (SOff 8 0) = rg_s RG ->
sh_ok SEGS dts_Bx1 dts_SHgs E (mrestrict (w_H W1) m1).
Proof.
intros ly1 S1 hp1 W1 m1 md1 E j HAR Hj HB Hm.
pose proof HGSB as (G1 & G2 & G3).
unfold dts_SHgs, sh_ok. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
rewrite <- (aview_rd_of SEGS).
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 m1 md1 (rg_s RG) (4 * ASRC) HAR HGSZ) as HRA.
split.
- intros x Hx. rewrite Z.add_0_r in Hx.
  destruct (HRA (x + ASRC * Z.of_nat j) ltac:(unfold ASRC in *; lia)) as (s & Hs & Hok).
  exists s. split.
  + unfold shadow_of_addr in *.
    replace (SHADOW_OFF + 12 * Z.of_nat j + x / 8)
      with (SHADOW_OFF + (x + ASRC * Z.of_nat j) / 8); [exact Hs|].
    unfold ASRC. replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.div_add by lia. lia.
  + unfold saddr_ok in *. unfold ASRC in Hok.
    replace ((x + 96 * Z.of_nat j) mod 8) with (x mod 8) in Hok; [exact Hok|].
    replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.mod_add by lia. reflexivity.
- intros a Ha. unfold SHADOW_OFF, ASRC, IMG_TOP in *. lia.
Qed.

(* a byte of the image is no byte of the table block: YCbqG.blk_img_x (the laws' client-image field); the AR text's
   0x10000 <= a < IMG_TOP band is read from the AR instance's image cover, which a generic ARx does not give *)
Lemma dtk_low_img_x : forall cx ly S hp (W : world SEGS) mem md a,
ARx ly S hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> in_img SEGS a -> dtk_low cx a.
Proof.
intros cx ly S hp W mem md a HAR Hin Ha.
pose proof (pa_img_range a Ha) as Hr.
pose proof asan_consts as (C1 & _).
assert (NT : ~ (dxG cx <= a < dxG cx + req_size ATABLE))
  by (intros Ht; exact (blk_img_x SEGS B ARx LAWS ly S hp W mem md _ _ a HAR Hin Ht Ha)).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in NT.
unfold dtk_low, ATABLE in *. lia.
Qed.

(* a live block's byte is in the address space and off g_s: g_s's bytes are image bytes (HG), a live block's are
   not (YCbqG.blk_img_x); the AR text read both from the image band *)
Lemma dtk_blk_off_x : forall ly S hp (W : world SEGS) mem md p n a,
ARx ly S hp W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + n ->
0 <= a < 2 ^ 64 /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros ly S hp W mem md p n a HAR Hin Ha.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (_ & H4 & Hc & _).
pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
pose proof asan_consts as (C1 & _).
split; [lia|].
intros Hg. apply (blk_img_x SEGS B ARx LAWS ly S hp W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))).
Qed.

Lemma dtk_low_blk_x : forall cx ly S hp (W : world SEGS) mem md L p n a,
ARx ly S hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S hp W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly S hp W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dtk_low, ATABLE; lia|].
intros He. apply (blk_img_x SEGS B ARx LAWS ly S hp W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dtk_gs_ok_x : forall cx ly S hp (W : world SEGS) mem md a,
ARx ly S hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S hp W mem md a HAR Hin Ha.
split; [apply (dtk_low_img_x cx ly S hp W mem md a HAR Hin); refine (proj1 (HG a _)); unfold inG, G_DR;
  apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
apply (dtk_errno_sep B RG HRGD HGSB HSD HSM). left. exact Ha.
Qed.

Lemma dtk_fp_entry_x : forall cx ly S hp (W : world SEGS) mem md e L,
ARx ly S hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S hp W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dtk_low_blk_x cx ly S hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, (dtk_key_ptrs_len B RG) in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dtk_fp_list_x : forall cx ly S hp (W : world SEGS) mem md L LA l lines,
ARx ly S hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S hp W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dtk_low_blk_x cx ly S hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dtk_gs_ok_x cx ly S hp W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, (dtk_recs_len B RG) in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dtk_fp_src_x : forall cx ly S hp (W : world SEGS) mem md L h,
ARx ly S hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S hp W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dtk_gs_ok_x cx ly S hp W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dtk_low_blk_x cx ly S hp W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dtk_fp_list_x cx ly S hp W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dtk_fp_list_x cx ly S hp W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dtk_fp_list_x cx ly S hp W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

(* the cells of G_DR and of the three output cells (HG / HGO) are image bytes; the AR text read them from the image band *)
Local Ltac dtk_gdr_x := lazymatch goal with IMG : forall x, in_img _ x -> _, GDR : forall x, inG (G_DR _ _) x -> _ |- _ =>
  apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] end.
Local Ltac dtk_go_x := lazymatch goal with IMG : forall x, in_img _ x -> _, GO : forall x, inG [_; _; _] x -> _ |- _ =>
  apply IMG, GO; unfold inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] end.
Lemma dtk_fp_out_x : forall cx ly S hp (W : world SEGS) mem md c O mx no cap out L,
ARx ly S hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dtk_low cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S hp W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, in_img SEGS x -> dtk_low cx x)
  by (intros x Hx; exact (dtk_low_img_x cx ly S hp W mem md x HAR GT Hx)).
assert (GDR : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GO : forall x, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x -> in_img SEGS x)
  by (intros x Hx; exact (proj1 (HGO x Hx))).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [dtk_go_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_gdr_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_gdr_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_gdr_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_go_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_gdr_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_go_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_gdr_x | intros _; apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); tauto].
- split; [dtk_gdr_x | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dtk_low_blk_x cx ly S hp W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

Lemma dtk_asrc_set_eintr_x : forall ly S hp (W : world SEGS) m m' md HA h,
ARx ly S hp W m md -> rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
asrc_at B ly S W m HA h ->
val_mem SEGS (arm W m') (HA + 12) 4 0 -> awr W m' (HA + 12) 4 ->
(forall x, HA <= x < HA + ASRC -> ~ (HA + 12 <= x < HA + 16) -> abyte_kept W m W m' x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (HA <= x < HA + ASRC) -> abyte_kept W m W m' x) ->
asrc_at B ly S W m' HA (dtk_set_eintr h).
Proof.
intros ly S hp W m m' md HA h HAR Hlo Hhi HS VE WE KIN KOUT.
assert (KB : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + n -> abyte_kept W m W m' x).
{ intros p n x Hin Hx. destruct (dtk_blk_off_x ly S hp W m md p n x HAR Hin Hx) as (Hx1 & Hx2).
  apply KOUT; [exact Hx1 | lia]. }
assert (KS : forall lo, HA <= lo -> lo + 16 <= HA + 96 -> HA + 16 <= lo ->
  forall x, lo <= x < lo + 16 -> abyte_kept W m W m' x).
{ intros lo H1 H2 H3 x Hx. apply KIN; [unfold ASRC; lia | lia]. }
assert (Hvm : forall a n v, HA <= a -> a + Z.of_nat n <= HA + 12 \/ HA + 16 <= a -> a + Z.of_nat n <= HA + 96 ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v).
{ intros a n v H1 H2 H3 Hv. apply (akept_vm W m); [|exact Hv]. intros x Hx. apply KIN; [unfold ASRC; lia | lia]. }
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
  H19 & H20 & H21 & H22 & H23 & H24).
unfold asrc_at, dtk_set_eintr.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
  hs_expected hs_held].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H3]|].
split; [exact VE|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i 12) as [Hi1|Hi1].
  - apply (proj2 (KIN (HA + i) ltac:(lia) ltac:(lia))). exact (H5 i Hi).
  - destruct (Z_lt_le_dec i 16) as [Hi2|Hi2].
    + replace (HA + i) with (HA + 12 + (i - 12)) by lia. exact (WE (i - 12) ltac:(lia)).
    + apply (proj2 (KIN (HA + i) ltac:(lia) ltac:(lia))). exact (H5 i Hi). }
split; [exact H6|]. split; [left; reflexivity|]. split; [exact H8|]. split; [exact H9|].
split; [exact (dtk_alist_kept B RG HGSB ly S W m m' (HA + 16) (hs_pending h) false H10
  (KS (HA + 16) ltac:(lia) ltac:(lia) ltac:(lia)) KB)|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|]. split; [exact H18|]. split; [exact H19|].
split.
{ apply (akept_garr8 W m); [|exact H20]. intros x Hx. apply (KB (hs_partial h) APARTIAL x H18).
  unfold bzs in Hx. rewrite length_map in Hx. lia. }
split; [exact H21|].
split; [exact (dtk_alist_kept B RG HGSB ly S W m m' (HA + 64) (hs_expected h) true H22
  (KS (HA + 64) ltac:(lia) ltac:(lia) ltac:(lia)) KB)|].
split; [exact (dtk_alist_kept B RG HGSB ly S W m m' (HA + 80) (hs_held h) true H23
  (KS (HA + 80) ltac:(lia) ltac:(lia) ltac:(lia)) KB)|].
exact H24.
Qed.

Lemma dt1_fp_entry_gs_x : forall ly S hp (W : world SEGS) mem md e,
ARx ly S hp W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros ly S hp W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> p <= a < p + n ->
  ~ (rg_s RG <= a < rg_s RG + 4 * ASRC)).
{ intros p n Hin Hpa.
  exact (proj2 (dtk_blk_off_x ly S hp W mem md p n a HAR
    (dtk_aentry_blks_in B RG HGSB ly S W mem e HE _ Hin) Hpa)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [|lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, (dt1_key_ptrs_len B RG) in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [|lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [|lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). exact Hk.
Qed.

Lemma dt1_fp_out_gs_x : forall ly S hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros ly S hp W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha;
  try (apply (dt1_gs_sep B RG HRGD HGSB HSD HSM); repeat first [left; lia | right]; lia).
destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
exact (proj2 (dtk_blk_off_x ly S hp W mem md out cap a HAR Hin ltac:(lia))).
Qed.

Lemma dt1_blk_args_x : forall ly S hp (W : world SEGS) mem md p n a,
ARx ly S hp W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + n ->
0 <= a < alloc_ceiling /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros ly S hp W mem md p n a HAR Hin Ha.
destruct (dtk_blk_off_x ly S hp W mem md p n a HAR Hin Ha) as (H64 & Hgs).
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
pose proof (@ASAN_CEIL_range rc) as (Hc & _). unfold ASAN_CEIL in Hceil.
split; [lia|]. split; [exact Hgs|].
intros He. apply (blk_img_x SEGS B ARx LAWS ly S hp W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dt1_seat_x : forall cx hp kr (W : world SEGS) regs m,
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
spZ regs = dsp0 cx - DRAIN_FRAME ->
getr regs 8 = w64 (rg_s RG) -> getr regs 23 = w64 (dHA RG cx) ->
getr regs 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
dr_frame RG cx W m ->
val_mem SEGS (arm W m) (dHA RG cx + 12) 4 1 ->
awr W m (dHA RG cx) ASRC ->
st_ok_pi SEGS VAL (Eimg (Ereg regs dt1_extra)) (dt1_ss (dxj cx))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_slot)) m (seg_rom SEGS))).
Proof.
intros cx hp kr W regs m HB Hsp R8 R23 R19 HFR VEI HAW.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs dt1_extra)).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs dt1_extra 0)).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E2 : ew E 2 = getr regs 2) by (apply EREG; [lia | reflexivity]).
assert (U2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG)
  by (rewrite E8; apply unsigned_lit_small; unfold IMG_TOP, ASRC in *; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small;
      unfold dHA, ASRC, IMG_TOP in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HHA : 0x10000 <= dHA RG cx /\ dHA RG cx + ASRC <= IMG_TOP) by (unfold dHA, ASRC, IMG_TOP in *; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, dts_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    exact (dtm_chunks_ok B RG HGSB cx W m E HFR E8 E32).
  + unfold region_ok, dt1_hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [lia|]. split; [unfold IMG_TOP, ASRC in *; lia|].
    split; [intros o Ho; exact (HAW o ltac:(unfold ASRC; lia))|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 12 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia | exact VEI].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, dts_frame, dt1_hs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23.
  split; [split; [right; unfold IMG_TOP, ASRC in *; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]].
  unfold dt1_facts, dts_IMGF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U19, U23, U32.
  assert (M16 : (dsp0 cx - DRAIN_FRAME) mod 2 ^ 4 = 0)
    by (change (2 ^ 4) with 16; rewrite HDF, Zminus_mod, Hal16; reflexivity).
  assert (M8 : rg_s RG mod 2 ^ 3 = 0) by exact G3.
  assert (M23 : dHA RG cx mod 2 ^ 3 = 0) by (unfold dHA; exact (dt1_mod8 B RG (rg_s RG) (dxj cx) G3)).
  rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
    unfold IMG_TOP, SHADOW_OFF, ASRC in *; lia.
Qed.

Lemma dt2_seat_x : forall cx hp kr (W : world SEGS) regs m (ei pn : Z),
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
spZ regs = dsp0 cx - DRAIN_FRAME ->
getr regs 8 = w64 (rg_s RG) -> getr regs 23 = w64 (dHA RG cx) ->
getr regs 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
dr_frame RG cx W m ->
val_mem SEGS (arm W m) (dHA RG cx + 12) 4 ei -> 0 <= ei < 2 ^ 32 ->
val_mem SEGS (arm W m) (dHA RG cx + 24) 4 pn -> 0 <= pn < 2 ^ 32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs dt2_extra)) (dt2_ss (dxj cx) ei pn)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_slot)) m (seg_rom SEGS))).
Proof.
intros cx hp kr W regs m ei pn HB Hsp R8 R23 R19 HFR VEI HEI VPN HPN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs dt2_extra)).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs dt2_extra 0)).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E2 : ew E 2 = getr regs 2) by (apply EREG; [lia | reflexivity]).
assert (U2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG)
  by (rewrite E8; apply unsigned_lit_small; unfold IMG_TOP, ASRC in *; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small;
      unfold dHA, ASRC, IMG_TOP in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HHA : 0x10000 <= dHA RG cx /\ dHA RG cx + ASRC <= IMG_TOP) by (unfold dHA, ASRC, IMG_TOP in *; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, dts_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    exact (dtm_chunks_ok B RG HGSB cx W m E HFR E8 E32).
  + unfold region_ok, dt2_hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [lia|]. split; [unfold IMG_TOP, ASRC in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ _ 12 4 (SLit ei) ei); [reflexivity | cbn; lia | cbn; lia | exact VEI].
    * apply (chunk_ok_val SEGS E _ _ 24 4 (SLit pn) pn); [reflexivity | cbn; lia | cbn; lia | exact VPN].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, dts_frame, dt2_hs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23.
  split; [split; [right; unfold IMG_TOP, ASRC in *; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]].
  unfold dt2_facts, dts_IMGF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U19, U23, U32.
  assert (M16 : (dsp0 cx - DRAIN_FRAME) mod 2 ^ 4 = 0)
    by (change (2 ^ 4) with 16; rewrite HDF, Zminus_mod, Hal16; reflexivity).
  assert (M8 : rg_s RG mod 2 ^ 3 = 0) by exact G3.
  assert (M23 : dHA RG cx mod 2 ^ 3 = 0) by (unfold dHA; exact (dt2_mod8 B RG (rg_s RG) (dxj cx) G3)).
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
    unfold IMG_TOP, SHADOW_OFF, ASRC in *; lia.
Qed.

Lemma dt3_blk_apart_x : forall ly S hp (W : world SEGS) mem md p n q m,
ARx ly S hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
dt3_apart p (req_size n) q (req_size m).
Proof.
intros ly S hp W mem md p n q m HAR Hp Hq Hne.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hk) as Hk0.
  exact (proj1 (req_size_pos k ltac:(lia))). }
pose proof (dt3_pw_nodup B RG _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros Eq; exact (Hne (dt3_nodup_map_inj f _ _ _ Hnd Hp Hq Eq))).
destruct (dt3_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hp) (in_map f _ _ Hq) Hf) as [X|X];
  unfold dt3_apart, zdisjoint, f in *; cbn [fst snd] in X; lia.
Qed.

Lemma dt3_ablocks_nodup_x : forall ly S hp (W : world SEGS) mem md, ARx ly S hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S hp W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hp : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hk) as Hk0.
  exact (proj1 (req_size_pos k ltac:(lia))). }
rewrite <- Eb. exact (NoDup_map_inv f _ (dt3_pw_nodup B RG _ Hpos Hpw)).
Qed.

(* a live block is apart from every range of g_s: its bytes are off the image (YCbqG.blk_img_x), g_s's are image
   bytes (HG); the AR text read the block's side from the image band (blk_off_imgP) *)
Lemma dt3_blk_gs_x : forall ly S hp (W : world SEGS) mem md q m a n,
ARx ly S hp W mem md -> In (q, m) (ablocks B ly S) -> rg_s RG <= a -> a + n <= rg_s RG + 4 * ASRC -> 0 < n ->
dt3_apart q (req_size m) a n.
Proof.
intros ly S hp W mem md q m a n HAR Hin Ha1 Ha2 Hn.
pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hin) as Hm0. pose proof (req_size_pos m Hm0) as [Hr1 _].
unfold dt3_apart.
destruct (Z_le_gt_dec (q + req_size m) a) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (a + n) q) as [H2|H2]; [right; exact H2|].
exfalso. apply (blk_img_x SEGS B ARx LAWS ly S hp W mem md q m (Z.max q a) HAR Hin ltac:(lia)).
apply (proj1 (HG (Z.max q a) ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))).
Qed.

(* lib/B/YCbq.v amem_range_of_block's proof, from the blocks law alx_blocks *)
Lemma dt3_amem_range_blk_x : forall ly S hp (W : world SEGS) mem md q m a n,
ARx ly S hp W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> a + n <= q + req_size m -> amem_range a n.
Proof.
intros ly S hp W mem md q m a n HAR Hin H1 H3.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q m HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.

Local Ltac dt3_reg_x HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Local Ltac dt3_awr_x Usp :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha;
      first [ lia | left; split; [unfold awr_byte; left; lia | lia] ] |]);
  apply awr_ok_x_nil.

Local Ltac dt3_rs_x HS E HHA E8 E19 E23 E32 cxx r c :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    let Hx := fresh "Hx" in
    let Hd := fresh "Hd" in
    let HS' := fresh "HS'" in
    dt3_reg_x HS r Hx;
    assert (Hd : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 c) (SLit 3)) (SOff 32 0))
      = getr (ms_regs mx) r)
      by (rewrite Hx; symmetry;
          apply (dt3_den_resh B RG HGSB E (rg_s RG) (Z.of_nat (dxj cxx)) c E8 E19 ltac:(rewrite <- HHA; exact E23) E32);
          unfold IMG_TOP, ASRC in *; lia);
    pose proof (ast_ok_pi_set_reg_fp E _ _ r _ HS eq_refl Hd) as HS';
    clear HS Hd Hx; rename HS' into HS;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS
  end.

Local Ltac dt3_trap_x Hc T := exfalso; rewrite T in Hc; discriminate.

Local Ltac dt3_nowrf_x Usp N :=
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]); try contradiction;
  subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
  clear - Hr N; unfold dt3_wfr in N; lia.

Lemma dt3_bufnot_x : forall ly1 S1 hp1 (W1 : world SEGS) m1 md1 cx e1 h1 ocap out1,
ARx ly1 S1 hp1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx) ->
re_cap e1 <> 0 ->
~ In (re_buf e1, re_cap e1) (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
  asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx).
Proof.
intros ly1 S1 hp1 W1 m1 md1 cx e1 h1 ocap out1 HAR HP Hc0.
pose proof (Permutation_NoDup HP (dt3_ablocks_nodup_x _ _ _ _ _ _ HAR)) as HND.
unfold aentry_blks in HND. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) Hc0) in HND. cbn [app] in HND.
apply List.NoDup_cons_iff in HND as [_ HND]. apply List.NoDup_cons_iff in HND as [Hbufnot _].
exact Hbufnot.
Qed.

Lemma dt3_pend_ne_x : forall ly1 S1 hp1 (W1 : world SEGS) m1 md1 cx e1 h1 ocap out1 b,
ARx ly1 S1 hp1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx) ->
re_cap e1 <> 0 -> In b (alist_blks (hs_pending h1)) -> b <> (re_buf e1, re_cap e1).
Proof.
intros ly1 S1 hp1 W1 m1 md1 cx e1 h1 ocap out1 b HAR HP Hc0 Hb X. subst b.
apply (dt3_bufnot_x ly1 S1 hp1 W1 m1 md1 cx e1 h1 ocap out1 HAR HP Hc0).
apply in_or_app; right. apply in_or_app; left. unfold asrc_blks. right. apply in_or_app; left. exact Hb.
Qed.

Lemma dt3_buf_awr_x : forall cx ly1 S1 hp1 (W1 : world SEGS) m1 md1 e1 h1 ocap out1 a,
ARx ly1 S1 hp1 W1 m1 md1 ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks ocap out1 ++ dxrest cx) ->
re_cap e1 <> 0 -> re_cap e1 <> ATABLE -> In (re_buf e1, re_cap e1) (ablocks B ly1 S1) ->
re_buf e1 <= a < re_buf e1 + re_cap e1 ->
awr_byte DRAIN_STK_x (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) ly1 [] a.
Proof.
intros cx ly1 S1 hp1 W1 m1 md1 e1 h1 ocap out1 a HAR HPQ0 HP1 Hc0 HcT Hbin Ha.
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
pose proof (dt3_bufnot_x ly1 S1 hp1 W1 m1 md1 cx e1 h1 ocap out1 HAR HP1 Hc0) as Hbufnot.
assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
- right. left. split.
  + apply (Permutation_in _ HPQ0) in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|Hin0];
      [injection X as X1 X2; exfalso; apply HcT; symmetry; exact X2|].
    assert (Hin3 : In (re_buf e1, re_cap e1)
      (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
    { apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
      apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
      apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; right; exact X|].
      exfalso. apply Hbufnot. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
      exact Hin0. }
    unfold dFP, dr_fp. apply inFP_cons. right. exists (re_buf e1, re_buf e1 + req_size (re_cap e1)).
    split; [unfold ablocks_fp; exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ Hin3)|].
    cbn [fst snd]. rewrite RQC. lia.
  + exists (re_buf e1), (re_cap e1). split; [exact Hbin | rewrite RQC; lia].
- right. right. left. exists (re_buf e1), (re_cap e1). split; [exact Hbin|].
  split; [exact Hnot0 | rewrite RQC; lia].
Qed.

(* ---- route R: the R twins of the tail's stretches (dt1_eintr_xR, dt2_end_xR, dt3_data_xR), of dr_toptail_xR and of
   the lemmas whose statements carry the journal or DMEM_x, over the R carriers (DI_xR, DEND_xR, DRB_xR, W_drain_topb_cx.v
   DT2_xR); the runs are the G runs (paj_run_x_xG), the branch paj_branch_xR, the errno and memcpy calls the R site
   lemmas aj_gx_entry_at_xR / aj_intrin_at_xR (strict contracts lifted by WLE_R).  The strict lemmas below
   are these twins at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Lemma dtm_frame_wr_xR : forall cx hp ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 o,
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 m1 md1 k1 ->
  0 <= o < DRAIN_FRAME -> writable_at SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o).
Proof.
  intros cx hp ly1 S1 hp1 W1 m1 md1 k1 o HJ Ho.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  assert (HFS : (DRAIN_FRAME <=? DRAIN_STK_x) = true) by reflexivity.
  apply Z.leb_le in HFS.
  unfold arm. apply apresent_writable. apply Hpres. lia.
Qed.

Lemma dtk_DMEM_kept_xR : forall cx hp ly1 S1 hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx hp ly1 S1 hp1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 HMEM HJ2 KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (Hkept : forall a, abyte_kept W1 m1 W1 m2 a).
{ intros a. split; [exact (KL a)|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKA : forall fp, akept W1 m1 W1 m2 fp) by (intros fp r Hr a Ha; exact (Hkept a)).
assert (HVM : forall a n v, val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v H. apply (akept_vm W1 m1); [intros x Hx; exact (Hkept x) | exact H]. }
split; [exact HJ2|].
split; [intros a Ha; rewrite (KL a); exact (Hrom a Ha)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  repeat match type of HFR with _ /\ _ => let A := fresh "A" in destruct HFR as [A HFR] end.
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVM; assumption | intros i Hi; apply HVM; exact (HFR i Hi) ]. }
split; [exact (dtk_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => KL x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact (dtk_aentry_okx_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  (dtk_aentry_blks_in B RG HGSB ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  (dtk_asrc_blks_in B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact (dtk_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.

Lemma dt1_dmem_xR : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF,
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
   ~ (as_errno B <= x < as_errno B + 4) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
asrc_at B ly1 S1 W1 mF (dHA RG cx) (dtk_set_eintr h1) ->
val_mem SEGS (arm W1 mF) (as_errno B) 4 4 ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 mF mdF k1 e1 (dtk_set_eintr h1) (dclr sg) out1 4 sent LB1.
Proof.
intros cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF HB HMEM HJF KEEP PRES HSRCF VERR.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : ARx ly1 S1 hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
pose proof asan_consts as (C1 & _). pose proof HGSB as (GS1 & GS2 & GS3).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HspA : alloc_ceiling + DRAIN_STK_x <= dsp0 cx) by lia.
assert (HspB : dsp0 cx <= 2 ^ 47) by lia.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
  by (unfold dHA, ASRC; lia).
assert (GIMG : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GSG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (ERG : forall x, as_errno B <= x < as_errno B + 4 -> inG (G_DR B RG) x)
  by (intros x Hx; unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]).
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= IMG_TOP).
{ pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B) ltac:(lia)))) as P0.
  pose proof (pa_img_range _ (GIMG _ (ERG (as_errno B + 3) ltac:(lia)))) as P3. unfold IMG_TOP. lia. }
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept (w_H W1) m1 mF x (PRES x) Hw)).
assert (KI : forall x, 0x10000 <= x < IMG_TOP -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx N1 N2. split; [apply KEEP; [unfold IMG_TOP in *; lia | exact N1 | exact N2
    | unfold IMG_TOP in *; lia] | unfold arm; apply writable_kept; apply PRES]. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. split; [apply KEEP;
    [lia | unfold dHA, ASRC, IMG_TOP in *; lia | unfold IMG_TOP in *; lia | lia]
  | unfold arm; apply writable_kept; apply PRES]. }
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> q <= x < q + n -> abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hx.
  destruct (dt1_blk_args_x ly1 S1 hp1 W1 m1 md1 q n x HAR Hin Hx) as (Hc & Hgs & Hne).
  split; [apply KEEP; [lia | unfold dHA, ASRC in *; lia | exact Hne | lia]
  | unfold arm; apply writable_kept; apply PRES]. }
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
pose proof HEOK as (_ & _ & Hpad1 & Hpad2 & _).
split; [exact HJF|].
split.
{ intros x Hx. rewrite KEEP; [exact (Hrom x Hx)
  | pose proof (pa_img_range _ (dt1_rom_img x Hx)); lia
  | intros Hy; apply (HGR x); [apply GSG; unfold dHA, ASRC in *; lia | exact Hx]
  | intros Hy; apply (HGR x); [apply ERG; exact Hy | exact Hx]
  | pose proof (pa_img_range _ (dt1_rom_img x Hx)); unfold IMG_TOP in *; lia]. }
split; [intros x Hx1 Hx2 Hx3 Hx4; apply PRES; exact (Hpres x Hx1 Hx2 Hx3 Hx4)|].
split; [exact Hframes|].
split.
{ apply (dt1_frame_kept B RG HGSB cx W1 m1 mF HFR).
  intros o n v Ho Hn Hv. apply (akept_vm W1 m1); [intros x Hx; apply KFR; lia | exact Hv]. }
split.
{ apply (dtk_garr8_kept W1 m1 W1 mF _ _ Hgarr). intros x Hx.
  unfold bzs in Hx. rewrite length_map in Hx.
  unfold entry_bytes, re_nheld in Hx.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, Hpad1, Hpad2 in Hx.
  exact (proj1 (KBL (dxG cx) ATABLE x HGin1 ltac:(unfold AENT, ATABLE in *; lia))). }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ apply (dtk_aentry_okx_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF e1 HEOK);
    [|exact (dtk_aentry_blks_in B RG HGSB ly1 S1 W1 m1 e1 HEOK)].
  intros r Hr x Hx.
  destruct (dtk_fp_entry_x cx ly1 S1 hp1 W1 m1 md1 e1
    (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)
    HAR Hperm (fun b Hb => in_or_app _ _ _ (or_introl Hb)) HEOK r Hr x Hx) as (Hlow & Hne).
  pose proof (dt1_fp_entry_gs_x ly1 S1 hp1 W1 m1 md1 e1 HAR HEOK r Hr x Hx) as Hgs.
  destruct Hlow as (Hx0 & _).
  split; [apply KEEP; [lia | unfold dHA, ASRC in *; lia | exact Hne | lia]
  | unfold arm; apply writable_kept; apply PRES]. }
split; [exact HSRCF|].
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KI;
      [unfold ASRC, IMG_TOP in *; lia | unfold dHA, ASRC in *; lia
      | apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); left; unfold ASRC in *; lia].
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KI;
      [unfold ASRC, IMG_TOP in *; lia | unfold dHA, ASRC in *; lia
      | apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); left; unfold ASRC in *; lia]. }
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as K1.
  assert (K2 : abyte_kept W1 m1 W1 mF x)
    by (apply KI; [unfold ASRC, IMG_TOP in *; lia | unfold ASRC in *; lia
        | apply (dtk_errno_sep B RG HRGD HGSB HSD HSM); left; exact Hx1]).
  split; [rewrite (proj1 K2); exact (proj1 K1)|].
  intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw. }
split.
{ pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AWERR & _).
  rewrite <- (dt1_dctl_ev cx (Z.of_nat (length (with_nul sent))) ev1 4).
  refine (dtk_aout_ev B RG HRGD HGSB HSD HSM ly1 S1 W1 m1 mF _ _ _ _ _ _ 4 Hout _ _ VERR _ _).
  - intros r Hr x Hx Hne.
    destruct (dtk_fp_out_x cx ly1 S1 hp1 W1 m1 md1 _ _ _ _ _ _
      (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)
      HAR Hperm
      (fun b Hb => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb))))))
      Hout r Hr x Hx) as (Hlow & _).
    pose proof (dt1_fp_out_gs_x ly1 S1 hp1 W1 m1 md1 _ _ _ _ _ _ HAR Hout r Hr x Hx) as Hgs.
    destruct Hlow as (Hx0 & _).
    split; [apply KEEP; [lia | unfold dHA, ASRC in *; lia | exact Hne | lia]
    | unfold arm; apply writable_kept; apply PRES].
  - intros Hc x Hx.
    assert (Hin : In (out1, drain_b_c.ds_ocap sg) (ablocks B ly1 S1)).
    { apply (dtk_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout). unfold aout_blks.
      rewrite (proj2 (Z.eqb_neq _ 0) Hc). left. reflexivity. }
    exact (proj2 (proj2 (dt1_blk_args_x ly1 S1 hp1 W1 m1 md1 out1 (drain_b_c.ds_ocap sg) x HAR Hin Hx))).
  - intros i Hi. apply HWK. exact (AWERR i Hi).
  - lia. }
split; [exact Hlivout | exact Hperm].
Qed.

Lemma dt1_eintr_xR : forall cx hp kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx hp kr -> DT2_xR B PST ARx MT RP MMAX RG R cx hp kr sg D W1 c1 ->
drain_b_c.ds_eintr sg = true ->
(forall W2 c2, DI_xR B PST ARx MT RP MMAX RG R cx hp kr (dclr sg) D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx hp kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx hp kr).
Proof.
intros cx hp kr sg D W1 c1 HB HT HEI K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
destruct HT as (regs1 & ly1 & S1 & hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & HRG & R23 & R19 & R10 & R13 & HM & HNZ & HUS & HDB & HL & HSAME & HH & HJ1 & HROOM & HLAT & HBUD).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HM as (HJ & HROM & HAPK & HFRS & HFR & HEB & HEW & HEX & HSRC & HOTH & HGK & HOUT & HDEAD & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & HSTK0 & _).
pose proof HSTK0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HSPA : alloc_ceiling + DRAIN_STK_x <= dsp0 cx) by lia.
assert (HSPB : dsp0 cx <= 2 ^ 47) by lia.
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
pose proof HL as (_ & _ & _ & _ & _ & HLE & _).
rewrite HEI in HLE.
pose proof HSRC as (_ & _ & _ & VEI & HAW & _).
rewrite HLE in VEI.
pose proof (dt1_seat_x cx hp kr W1 regs1 m1 HB Hsp R8 R23 R19 HFR VEI HAW) as HS.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
remember (Eimg (Ereg regs1 dt1_extra)) as E eqn:HE.
assert (HEIE : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 dt1_extra 0)).
assert (UB1 : U E dts_Bx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dts_Bx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19
      | unfold SHADOW_OFF; lia]).
assert (U8 : U E (SOff 8 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8
      | unfold IMG_TOP, ASRC in *; lia]).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small;
      unfold dHA, ASRC, IMG_TOP in *; lia).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (SHOK : sh_ok SEGS dts_Bx1 dts_SHgs E (mrestrict (w_H W1) m1))
  by exact (dts_shent_gs_x ly1 S1 hp1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U8).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
revert HS. destruct (dxj cx) as [|[|[|[|jj]]]] eqn:Ej; [| | | | exfalso; lia]; intros HS.
all: paj_run_tok_xR RUNG HS HJ SHOK dts_Bspan;
  [ cbn [ss_mem dt1_ss];
    apply awr_ok_x_cons;
    [ intros x Hx; exfalso; cbn [dts_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia | ];
    apply awr_ok_x_cons_g; [ | apply awr_ok_x_nil ];
    intros x Hx; cbn [dt1_hs YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U23 in Hx;
    unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold dHA, ASRC in *; lia | ].
all: pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as RF1; cbn [ms_mem restrict] in RF1.
all: assert (V12A : val_mem SEGS (arm W1 (ms_mem ms)) (dHA RG cx + 12) 4 0);
  [ unfold arm;
    pose proof (field_of_region E (mrestrict (w_H W1) (ms_mem ms)) 23%nat (dHA RG cx) _ 12 16 12 16 12
      4%N (SLit 0) 0 RF1) as VF;
    apply VF; [exact U23 | left; reflexivity | reflexivity | cbn; lia | cbn; lia] | ].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
all: eapply (YA0nH.SRrG_bind SEGS R R_trans);
  [ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
    [ unfold spZ at 1; rewrite Q2, Usp; lia
    | reflexivity
    | unfold DRAIN_FRAME; lia
    | lia
    | unfold ESTACK, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | rewrite Q3, (EREG 3%nat 3%bv), R3 by (first [lia | reflexivity]); exact Hgp
    | rewrite Q4, (EREG 4%nat 4%bv), R4 by (first [lia | reflexivity]); exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros x; right; intros []
    | intros x []
    | intros x []
    | intros HPRE2 _; exact (AERRNO ly1 S1 hp1 W1 (ms_regs ms) (ms_mem ms) _ HPRE2) ] |].
all: cbv beta; intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
all: jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0]%nat HS2.
all: match type of HS2 with ?ty -> _ =>
  assert (HRK : ty) by
    (cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
     split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros aa Haa;
     [ apply (mbyte_of_aview SEGS); apply Hfr2;
       [ lia | intros [] | lia ]
     | exfalso; lia ]);
  specialize (HS2 HRK); clear HRK end.
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 33 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
all: assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEIE | cbv; lia]).
all: assert (OLDa : forall n, (n < 33)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
all: clear HEa.
all: pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAWE & _).
all: prreg HS (10%bv : bv 5) R10a.
all: assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= IMG_TOP);
  [ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i));
    [ intros i Hi; apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
        repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ])))
    | pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0;
      pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3; unfold IMG_TOP; lia ] | ].
all: assert (F37 : ew Ea 37 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10a, Herr, HERRNO; reflexivity).
all: assert (B37 : bv_unsigned (ew Ea 37) = as_errno B)
  by (rewrite F37; apply unsigned_lit_small; unfold IMG_TOP in *; lia).
all: apply (st_ok_pi_add_fact _ _ _ 37%nat (mkAF 0x10000 IMG_TOP 2)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B37;
     split; [unfold IMG_TOP in *; lia|]; split; [change (2 ^ 2) with 4; exact HERRAL | lia] ].
all: apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 37%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B37; split; [unfold IMG_TOP in *; lia|]; split; [unfold IMG_TOP in *; lia|];
      split; [|apply Forall_nil];
      intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
      [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (HAWE o Ho) ]
    | cbn [ss_mem add_atom all_disjoint]; unfold extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite B37, (OLDa 2%nat ltac:(lia)), Usp;
      split; [left; unfold IMG_TOP in *; lia | exact I] ].
all: assert (UB2 : U Ea dts_Bx2 = SHADOW_OFF)
  by (unfold dts_Bx2; apply U_atom;
      [ rewrite (OLDa 32%nat) by lia; exact E32 | unfold SHADOW_OFF; lia ]).
all: assert (UE37 : U Ea (SOff 37 0) = as_errno B)
  by (apply U_atom; [exact F37 | unfold IMG_TOP in *; lia]).
all: assert (SHOK2 : sh_ok SEGS dts_Bx2 dt1_SH2 Ea (mrestrict (w_H W1) mem2));
  [ unfold sh_ok, dt1_SH2; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dts_Bx2 37%nat (as_errno B) 4 (as_errno B) 0 4);
    [ apply (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem2 md2 (as_errno B) 4);
      [ exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) | exact HERRZ ]
    | exact UB2 | exact UE37 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF, IMG_TOP in *; lia ] | ].
all: paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 dts_Bspan A_dr_top;
  [ cbn [ss_mem];
    apply awr_ok_x_cons_g;
    [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite B37 in Hx;
      unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
    | apply awr_ok_x_cons;
      [ intros x Hx; exfalso;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
      | apply awr_ok_x_nil ] ] | ].
all: rename HFr into FR3; rename HG0 into GR3; clear HF.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: assert (KL2 : forall x, 0 <= x < 2 ^ 64 -> ~ (as_errno B <= x < as_errno B + 4) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) mem2 x);
  [ intros x Hx0 Hx; apply (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms0) FR3 x Hx0);
    intros (r & Hin & Hr); cbn [ss_mem add_atom In] in Hin; destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [ rewrite B37 in Hr; lia | lia ] | ].
all: assert (KL1 : forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x);
  [ intros x Hx0 Hx; apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 x Hx0);
    intros (r & Hin & Hr); cbn [ss_mem dt1_ss In] in Hin; destruct Hin as [<- | [<- | []]];
    unfold dts_frame, dt1_hs in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [ lia | rewrite U23 in Hr; lia ] | ].
all: assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ (as_errno B <= x < as_errno B + 4) ->
  ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) (ms_mem ms) x);
  [ intros x H1 H2 H3; rewrite (KL2 x H1 H2); apply Hfr2; [exact H1 | intros [] | lia] | ].
all: assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
  ~ (as_errno B <= x < as_errno B + 4) ->
  ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) m1 x);
  [ intros x H1 H2 H3 H4; rewrite (KEEP2 x H1 H3 H4); exact (KL1 x H1 H2) | ].
all: assert (PRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms0) x);
  [ intros x Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2;
    apply (apresent_grows _ _ _ _ GR1); exact Hp | ].
all: assert (AWR12 : awr W1 (ms_mem ms) (dHA RG cx + 12) 4);
  [ intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 (ms_mem ms));
    [ apply (apresent_grows _ _ _ _ GR1) | ];
    replace (dHA RG cx + 12 + i) with (dHA RG cx + (12 + i)) by lia;
    exact (HAW (12 + i) ltac:(unfold ASRC; lia)) | ].
all: assert (HSRCA : asrc_at B ly1 S1 W1 (ms_mem ms) (dHA RG cx) (dtk_set_eintr h1));
  [ apply (dtk_asrc_set_eintr_x ly1 S1 hp1 W1 m1 (ms_mem ms) md1 (dHA RG cx) h1 HAR
      ltac:(unfold dHA, ASRC; lia) ltac:(unfold dHA, ASRC; lia) HSRC V12A AWR12);
    [ intros x Hx N; split;
      [ apply KL1; [unfold dHA, ASRC, IMG_TOP in *; lia | exact N]
      | unfold arm; apply writable_kept; apply (apresent_grows _ _ _ _ GR1) ]
    | intros x Hx N; split;
      [ apply KL1; [exact Hx | unfold dHA, ASRC in *; lia]
      | unfold arm; apply writable_kept; apply (apresent_grows _ _ _ _ GR1) ] ] | ].
all: assert (HSRCF : asrc_at B ly1 S1 W1 (ms_mem ms0) (dHA RG cx) (dtk_set_eintr h1));
  [ apply (asrc_at_kept B ly1 S1 W1 (ms_mem ms) ly1 S1 W1 (ms_mem ms0) (dHA RG cx)
      (dtk_set_eintr h1) HSRCA);
    [ intros r Hr x Hx;
      destruct (dtk_fp_src_x cx ly1 S1 hp1 W1 m1 md1
        (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)
        h1 HAR HPERM (fun b Hb => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb))))
        HGin ltac:(rewrite Ej; lia) HSRC r Hr x Hx) as ((Hx0 & _) & Hne);
      split; [ exact (KEEP2 x ltac:(lia) Hne ltac:(lia))
             | unfold arm; apply writable_kept;
               intros Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2; exact Hp ]
    | intros b Hb; exact (dtk_asrc_blks_in B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 HSRC b Hb) ] | ].
all: assert (VERR : val_mem SEGS (arm W1 (ms_mem ms0)) (as_errno B) 4 4);
  [ unfold arm;
    pose proof (field_of_region _ (mrestrict (w_H W1) (ms_mem ms0)) 37%nat (as_errno B) _ 0 4 0 4 0
      4%N (SLit 4) 4 RF) as VF;
    rewrite Z.add_0_r in VF; apply VF;
    [ rewrite !ew_ewset_other by lia; exact B37 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] | ].
all: pose proof (dt1_dmem_xR cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1
  (ms_mem ms0) (with_vm_backing (m_vm_lazy md2) mat0 md2) HB HM HJ2 KEEP PRES HSRCF VERR) as HM2.
all: pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
all: assert (HLF : DLINK (dclr sg) e1 (dtk_set_eintr h1));
  [ unfold DLINK, dclr, dtk_set_eintr;
    cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
         drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en
         drain_b_c.ds_ecap hs_eintr hs_pending hs_off hs_expected];
    split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|];
    split; [exact L5|]; split; [reflexivity|]; split; [exact L7|]; split; [exact L8|];
    split; [exact L9|]; split; [exact L10|]; split; [exact L11 | exact L12] | ].
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4;
  prreg HS (8%bv : bv 5) X8; prreg HS (9%bv : bv 5) X9; prreg HS (18%bv : bv 5) X18;
  prreg HS (20%bv : bv 5) X20; prreg HS (21%bv : bv 5) X21; prreg HS (22%bv : bv 5) X22;
  prreg HS (24%bv : bv 5) X24; prreg HS (26%bv : bv 5) X26; prreg HS (27%bv : bv 5) X27.
all: pmkst HS.
all: apply K.
all: exists (ms_regs ms0), ly1, S1, hp1, (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2), k1, e1,
  (dtk_set_eintr h1), out1, 4, LB1, spent, jb, a, tl.
all: split; [reflexivity|].
all: split;
  [ split; [unfold spZ; rewrite X2, OLDa by lia;
            rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|];
    split; [rewrite X3, OLDa by lia; rewrite (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|];
    split; [rewrite X4, OLDa by lia; rewrite (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|];
    split; [rewrite X21, OLDa by lia; rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|];
    split; [rewrite X24, OLDa by lia; rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24|];
    split; [rewrite X20, OLDa by lia; rewrite (EREG 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|];
    split; [rewrite X22, OLDa by lia; rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); exact R22|];
    split; [rewrite X27, OLDa by lia; rewrite (EREG 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|];
    split; [rewrite X8, OLDa by lia; rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|];
    split; [rewrite X9, OLDa by lia; rewrite (EREG 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|];
    split; [rewrite X18, OLDa by lia; rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|];
    rewrite X26, OLDa by lia; rewrite (EREG 26%nat 26%bv) by (first [lia | reflexivity]); exact R26 | ].
all: split; [exact HM2|].
all: split; [exact HNZ|].
all: split; [exact HUS|].
all: split; [intros _; exact HDB|].
all: split; [exact HLF|].
all: split; [exact HSAME|].
all: split; [exact HH|].
all: split; [exact HJ1|].
all: split; [exact (dtm_later_dclr B RG HGSB cx sg jb a tl L12 HROOM HEI HLAT) | exact HBUD].
Qed.

Lemma dt2_end_xR : forall cx hp kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx hp kr -> DT2_xR B PST ARx MT RP MMAX RG R cx hp kr sg D W1 c1 ->
drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg = [] ->
(forall W2 c2, DEND_xR B PST ARx MT RP MMAX RG R cx hp kr sg D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx hp kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx hp kr).
Proof.
intros cx hp kr sg D W1 c1 HB HT HEF HPD K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
destruct HT as (regs1 & ly1 & S1 & hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & HRG & R23 & R19 & R10 & R13 & HM & HNZ & HUS & HDB & HL & HSAME & HH & HJ1 & HROOM & HLAT & HBUD).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HM as (HJ & _ & _ & _ & HFR & _ & _ & _ & HSRC & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HL as (_ & _ & _ & _ & _ & HLE & _).
rewrite HEF in HLE.
assert (HREC : hl_recs (hs_pending h1) = []) by exact (proj1 (dts_pend_recs sg e1 h1 HL) HPD).
pose proof HSRC as (_ & _ & _ & VEI & _ & _ & _ & _ & _ & HPL & _).
pose proof HPL as (_ & VPN & _).
rewrite HLE in VEI.
unfold hl_n in VPN. rewrite HREC in VPN. cbn [length Z.of_nat] in VPN.
replace (dHA RG cx + 16 + 8) with (dHA RG cx + 24) in VPN by lia.
pose proof (dt2_seat_x cx hp kr W1 regs1 m1 0 0 HB Hsp R8 R23 R19 HFR VEI ltac:(lia) VPN ltac:(lia)) as HS.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
remember (Eimg (Ereg regs1 dt2_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (UB1 : U E dts_Bx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dts_Bx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19
      | unfold SHADOW_OFF; lia]).
assert (U8 : U E (SOff 8 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8
      | unfold IMG_TOP, ASRC in *; lia]).
assert (SHOK : sh_ok SEGS dts_Bx1 dts_SHgs E (mrestrict (w_H W1) m1))
  by exact (dts_shent_gs_x ly1 S1 hp1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U8).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
revert HS. destruct (dxj cx) as [|[|[|[|jj]]]] eqn:Ej; [| | | | exfalso; lia]; intros HS.
all: paj_run_to_tok_xR RUNTOG HS HJ SHOK dts_Bspan A_dr_end; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: assert (KL : forall x, aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x);
  [ intros x; apply (aview_eq_of SEGS); apply FR1; intros (r & Hin & Hr);
    cbn [ss_mem dt2_ss In] in Hin; destruct Hin as [<- | [<- | []]];
    unfold dts_frame, dt2_hs in Hr; cbn [YP09.r_wlo YP09.r_whi] in Hr; lia | ].
all: assert (KP : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR1 Hp)).
all: pose proof (dtk_DMEM_kept_xR cx hp ly1 S1 hp1 W1 m1 (ms_mem ms) md1 _ k1 k1 e1 h1 sg out1 ev1 _ LB1 HM HJ KL KP)
  as HM2.
all: pose proof HM2 as (_ & _ & _ & _ & HFR2 & _).
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4;
  prreg HS (19%bv : bv 5) X19; prreg HS (21%bv : bv 5) X21; prreg HS (23%bv : bv 5) X23.
all: pmkst HS.
all: apply K.
all: exists (ms_regs ms), ly1, S1, hp1, (ms_mem ms), (with_vm_backing (m_vm_lazy md1) mat md1), k1, e1, h1, out1, ev1, LB1,
  spent, jb, a, tl.
all: split; [reflexivity|].
all: split; [unfold spZ; rewrite X2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
all: split; [rewrite X3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
all: split; [rewrite X4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
all: split; [rewrite X21, (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
all: split; [rewrite X23, (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23|].
all: split; [rewrite X19, (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite Ej; exact R19|].
all: split; [exact HFR2|].
all: split; [exact HM2|].
all: exact (conj HNZ (conj HUS (conj HL (conj HSAME (conj HH (conj HJ1 (conj HPD (conj HEF (conj HROOM
  (conj HLAT HBUD)))))))))).
Qed.

Lemma dt3_dmem_drb_xR : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF (data : list byte),
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
0 < re_cap e1 -> (length data <= length (re_junk e1))%nat ->
(forall x, 0 <= x < 2 ^ 64 ->
   ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
   ~ (dsp0 cx - DRAIN_STK_x <= x < dsp0 cx) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
(forall i, (i < length data)%nat ->
   aview SEGS (w_H W1) mF (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)) ->
dr_frame RG cx W1 mF ->
DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W1 mF mdF k1 (dt3_junk e1 (data ++ skipn (length data) (re_junk e1))) h1 sg out1 ev1 sent LB1.
Proof.
intros cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF data HB HMEM HJF Hcp Hdl KEEP PRES CPY HFRF.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR : ARx ly1 S1 hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & _ & Hj4 & _).
pose proof Hafn as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
assert (HspA : alloc_ceiling + 17008 <= dsp0 cx) by (unfold dsp0; rewrite HDS in Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
pose proof HGSB as (GS1 & GS2 & GS3).
pose proof HEOK as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
  HND1 & HND2 & Hkeys).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [lia|].
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & _). rewrite RQC in Hbceil.
assert (HDL : Z.of_nat (length data) <= re_cap e1 - re_used e1) by (rewrite <- Hjl; lia).
assert (Hul : 0 <= re_used e1) by lia.
assert (KBL : forall q n x, In (q, n) (ablocks B ly1 S1) -> (q, n) <> (re_buf e1, re_cap e1) -> q <= x < q + n ->
  abyte_kept W1 m1 W1 mF x).
{ intros q n x Hin Hne Hx. destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos n (BLKN _ _ _ _ _ _ _ _ HAR Hin)) as (_ & Rq).
  pose proof (dt3_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hin Hbin Hne) as Hap. rewrite RQC in Hap.
  split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP; unfold dt3_apart in *; lia. }
(* an image byte is kept: the copy's bytes are the relay buffer's, a live block, off the image (YCbqG.blk_img_x) *)
assert (KI : forall x, in_img SEGS x -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. pose proof (pa_img_range x Hx) as Hr.
  split; [|unfold arm; apply writable_kept; apply PRES].
  apply KEEP;
    [ lia
    | intros Hy; apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 m1 md1 _ _ x HAR Hbin); [rewrite RQC; lia | exact Hx]
    | lia ]. }
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HWK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 mF) x)
  by (intros x Hw; unfold arm in *; exact (writable_kept _ m1 mF x (PRES x) Hw)).
pose proof (Permutation_NoDup Hperm (dt3_ablocks_nodup_x _ _ _ _ _ _ HAR)) as HNDp.
unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by lia. cbn [app] in HNDp.
apply List.NoDup_cons_iff in HNDp as [HGnot HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot _].
assert (INB : forall b, In b (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). right. unfold aentry_blks.
  rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by lia. cbn [app]. right. exact Hb. }
assert (KH : forall q n x, In (q, n) (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
    map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
    asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx) -> q <= x < q + n ->
    abyte_kept W1 m1 W1 mF x).
{ intros q n y Hb Hy. apply (KBL q n y (INB _ Hb)); [|exact Hy].
  intros Heq. apply Hbufnot. rewrite <- Heq. exact Hb. }
split; [exact HJF|].
split; [intros x Hx; rewrite (proj1 (KI x (dt3_rom_img x Hx))); exact (Hrom x Hx)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply PRES; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split; [exact HFRF|].
assert (KEEPB : forall x, 0 <= x < 2 ^ 64 ->
  ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
  ~ (dsp0 cx - DRAIN_STK_x <= x < dsp0 cx) -> abyte_kept W1 m1 W1 mF x)
  by (intros x Hx N1 N2; split; [apply KEEP; assumption | unfold arm; apply writable_kept; apply PRES]).
split.
{ replace (entry_bytes (dt3_junk e1 (data ++ skipn (length data) (re_junk e1)))) with (entry_bytes e1)
    by reflexivity.
  apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx.
  rewrite (dt3_entry_len e1 Hpad1 Hpad2) in Hx.
  apply (KBL (dxG cx) ATABLE x HGin1
    ltac:(intros X; injection X as X1 X2; unfold ATABLE in *; lia)
    ltac:(unfold AENT, ATABLE in *; lia)). }
split; [intros i Hi; apply HWK; exact (Hawr i Hi)|].
split.
{ unfold aentry_okx, dt3_junk.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
  split; [exact Heof|]. split; [exact Hskip|]. split; [exact Hpad1|]. split; [exact Hpad2|].
  split; [exact Hfd|]. split; [exact Hcapr|]. split; [exact HUlen|]. split; [exact Husedc|].
  split.
  { right. split; [exact Hcpos|]. split; [exact Hbin|].
    split; [rewrite length_app, length_skipn; lia|].
    rewrite dt3_bzs_app in Hbuf8. apply garr8_app in Hbuf8 as [GU GJ].
    rewrite dt3_bzs_len, HUlen in GJ.
    rewrite !dt3_bzs_app. apply garr8_app. split.
    - apply (akept_garr8 W1 m1); [|exact GU]. intros x Hx. rewrite dt3_bzs_len in Hx.
      apply KEEPB; lia.
    - rewrite dt3_bzs_len, HUlen. apply garr8_app. split.
      + apply (dt3_garr8_of_aview B RG); [|apply (dt3_bzs_range B RG data)].
        intros i Hi. rewrite dt3_bzs_len in Hi. exact (CPY i Hi).
      + rewrite dt3_bzs_len.
        pose proof (dt3_garr8_skipn _ _ _ (length data) GJ ltac:(rewrite dt3_bzs_len; exact Hdl)) as GJ'.
        rewrite dt3_skipn_bzs in GJ'.
        apply (akept_garr8 W1 m1); [|exact GJ']. intros x Hx.
        rewrite dt3_bzs_len, length_skipn in Hx. apply KEEPB; lia. }
  split; [exact Hnheld|].
  split.
  { destruct Hheld as [H0 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H0 | right].
    split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx.
    apply (KH (re_hp e1) (re_kh e1)); [apply in_or_app; left; apply in_or_app; left;
      rewrite (proj2 (Z.eqb_neq _ 0) Hz); left; reflexivity|].
    unfold bzs in Hx. rewrite length_map, (dt3_key_ptrs_len B RG) in Hx. unfold re_nheld in Hk1. lia. }
  split; [exact HND1|]. split; [exact HND2|].
  rewrite Forall_forall in Hkeys |- *. intros k Hk. destruct (Hkeys k Hk) as (K1 & K2 & K3).
  split; [exact K1|]. split; [|exact K3].
  apply (akept_garr8 W1 m1); [|exact K2]. intros x Hx.
  apply (KH (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
  - apply in_or_app. left. apply in_or_app. right.
    exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hk).
  - unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia. }
assert (KGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 mF x).
{ intros x Hx. apply KI. apply (proj1 (HG x ltac:(unfold G_DR, inG; apply Exists_cons_hd;
    unfold in_zr; cbn [fst snd]; exact Hx))). }
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 4 * ASRC)
  by (unfold dHA, ASRC; lia).
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 mF (dHA RG cx) h1 Hsrc);
    [|exact (dtk_asrc_blks_in B RG HGSB ly1 S1 W1 m1 _ _ Hsrc)].
  intros r Hr x Hx. destruct (dt3_asrc_fp_in B RG HGSB _ _ _ _ _ _ Hsrc r Hr x Hx) as [X | (q & n & Hq & Hqx)].
  - apply KGS. lia.
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. left. exact Hq. }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & Vf & Vo & Hd). exists f, o.
  split; [|split; [|exact Hd]].
  - apply (akept_vm W1 m1); [|exact Vf]. intros x Hx. cbn in Hx. apply KGS. unfold ASRC in *. lia.
  - apply (akept_vm W1 m1); [|exact Vo]. intros x Hx. cbn in Hx. apply KGS. unfold ASRC in *. lia. }
split.
{ intros x Hx1 Hx2. destruct (Hgsk x Hx1 Hx2) as (Kv & Kw). destruct (KGS x Hx1) as (Kv2 & Kw2).
  split; [rewrite Kv2; exact Kv | intros Hw; exact (Kw2 (Kw Hw))]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 mF); [exact Hout | |
    exact (dtk_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout)].
  intros r Hr x Hx. destruct (dt3_aout_fp_in B RG HG HGO _ _ r Hr x Hx) as [Hi | (q & n & Hq & Hqx)].
  - exact (KI x Hi).
  - apply (KH q n x); [|exact Hqx]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hq. }
split; [exact Hlivout | exact Hperm].
Qed.

Lemma dt3_data_xR : forall cx hp kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx hp kr -> DT2_xR B PST ARx MT RP MMAX RG R cx hp kr sg D W1 c1 ->
drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg <> [] ->
(forall W2 c2, DRB_xR B PST ARx MT RP MMAX RG R cx hp kr sg D 0 W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx hp kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx hp kr).
Proof.
intros cx hp kr sg D W1 c1 HB HT2 Hei Hpne Krb.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
destruct HT2 as (regs1 & ly1 & S1 & hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & HR & R23 & R19 & R10 & R13 & HMEM & HnoNUL & Hused & Hinb & HLINK & HSAME & HHIST & HJ1 & Hroom &
  Hlater & Hbud).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HR as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HB as (Hafn & HB10 & HBG & HGSA & HSAG & HSA8 & HBgarr & HBawr & HBeok & Hj4 & HBsrc & HBoth & HBfd &
  HBsk & HBsk0 & HBout & HBrom & HPERM0 & HBps & HBcap & HBnh & HBtr & HBbb & HBmo).
clear HB10 HBG HSA8 HBgarr HBawr HBeok HBsrc HBoth HBfd HBsk HBsk0 HBout HBrom HBps HBcap HBnh HBtr HBbb HBmo.
pose proof Hafn as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HspA : alloc_ceiling + DRAIN_STK_x <= dsp0 cx) by (unfold dsp0; lia).
(* the AR lemmas cited below (dt3_seat1, dt3_frame_kept) read the AR width DRAIN_STK, 128 bytes below DRAIN_STK_x *)
assert (HspA0 : alloc_ceiling + DRAIN_STK <= dsp0 cx) by (clear - HspA; unfold DRAIN_STK_x in HspA; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
assert (HAR : ARx ly1 S1 hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HGin1) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAhi : dxSA cx + AENT <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof Hsrc as (V0 & V4 & V8 & V12 & HAWS & Hcl01 & Hei01 & Hopen & Hfdr & HPEND & V32 & V40 & V48 & V56 &
  Hrecs & Hnpart & Hovl & Hpin & Hpjl & Hpg & HnoW & HEXP & HHELD & HNDB).
pose proof HPEND as (P0 & P8 & P12 & PAW & Pn & Pv & PND & Pnv & Precs).
pose proof HLINK as (Lcap & Lu & Lsk & LH & Lka & Lei & Lpend & Loff & Lst & Len & Lecap & Lwf).
pose proof HOKX as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedc & Hbufc & Hnheld & Hheld &
  HND1 & HND2 & Hkeys).
assert (Hei0 : hs_eintr h1 = 0) by (rewrite Lei, Hei; reflexivity).
rewrite Hei0 in V12.
clear Hcl01 Hei01 Hovl Heof Hskip Hheld.
destruct Hrecs as [(Hnil & _) | (r0 & rs0 & Erecs & Hoff0 & HoffL)].
{ exfalso. apply Hpne. rewrite <- Lpend, Hnil. reflexivity. }
set (v := hl_v (hs_pending h1)) in *. set (off := hs_off h1) in *.
set (p := fst r0). set (len := Z.of_nat (length (snd r0))).
set (room := re_cap e1 - re_used e1).
assert (Hn1 : 1 <= hl_n (hs_pending h1) <= 2 ^ 30).
{ split; [|lia]. unfold hl_n. rewrite Erecs. cbn [length]. lia. }
destruct Pv as [(Hcap0 & _) | (Hcpv & Hvin & Hjv & Hvg)]; [exfalso; lia|].
rewrite Erecs in Hvg.
pose proof Precs as Precs'. rewrite Forall_forall in Precs'.
destruct (Precs' r0 ltac:(rewrite Erecs; left; reflexivity)) as (Hr0in & Hr0g & _ & Hr0len).
specialize (Hr0len eq_refl). clear Precs'.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hr0in) as (_ & Hs4096 & Hsceil & _).
pose proof (req_size_pos (len + 1) ltac:(lia)) as (_ & Rq0).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hvin) as (_ & Hv4096 & Hvceil & Hvapp & _).
pose proof (req_size_pos (AREC * hl_cap (hs_pending h1)) ltac:(unfold AREC; lia)) as (_ & Rqv).
assert (Hpb : 4096 <= p <= 140737479966720) by (unfold p; unfold len in *; lia).
assert (Hlb : 1 <= len <= 2 ^ 47) by (unfold len in *; lia).
assert (Hob : 0 <= off < len) by (unfold off, len in *; lia).
assert (Hul : ulen sg = re_used e1) by (unfold ulen; rewrite <- Lu; unfold bzs; rewrite length_map; exact HUlen).
assert (Hroom2 : 4096 <= room).
{ unfold room. rewrite <- Hul. rewrite <- Lcap in Hroom. exact Hroom. }
assert (Hcapb : re_cap e1 <= 16384) by lia.
assert (Hroomb : 0 < room <= 16384) by (unfold room; lia).
clear Hcapr.
unfold room in Hroom2.
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjl & Hbuf8)]; [exfalso; lia|].
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in Hbceil.
assert (Hpend0 : drain_b_c.ds_pend sg = bzs (snd r0) :: map (fun r => bzs (snd r)) rs0)
  by (rewrite <- Lpend, Erecs; reflexivity).
assert (Hdhead : dhead sg = bzs (snd r0)) by (unfold dhead; rewrite Hpend0; reflexivity).
assert (Hdn : dnum sg = Z.min (len - off) room).
{ unfold dnum. rewrite Hdhead. unfold bzs. rewrite length_map. rewrite <- Loff, <- Lcap, Hul.
  unfold len, off, room. reflexivity. }
set (dn := dnum sg) in *.
assert (Hdnr : 1 <= dn <= 16384) by (rewrite Hdn; lia).
assert (Hdnl : dn <= len - off) by (rewrite Hdn; lia).
assert (Hdnc : dn <= room) by (rewrite Hdn; lia).
assert (Hdnh : dt3_hide (dn = Z.min (len - off) room)) by exact Hdn.
clear Hdn.
assert (Hmod8 : p mod 8 = 0).
{ destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hr0in) as (H16 & _).
  apply Z.mod_divide in H16; [|lia]. destruct H16 as (q & Hq). unfold p. rewrite Hq.
  replace (q * 16) with (0 + (2 * q) * 8) by lia. apply dt3_mod_addk; [lia | reflexivity]. }
destruct (dt3_rec_vm B RG HGSB (arm W1 m1) v r0 rs0 _ Hvg ltac:(unfold p in Hpb; lia) ltac:(unfold len in *; lia))
  as (VP & VL).
assert (V16 : val_mem SEGS (arm W1 m1) (dHA RG cx + 16) 8 v) by exact P0.
assert (V24 : val_mem SEGS (arm W1 m1) (dHA RG cx + 24) 4 (hl_n (hs_pending h1)))
  by (replace (dHA RG cx + 24) with (dHA RG cx + 16 + 8) by lia; exact P8).
assert (HW : forall o, 0 <= o < DRAIN_FRAME -> writable_at SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o))
  by (intros o Hoo; exact (dtm_frame_wr_xR cx hp ly1 S1 hp1 W1 m1 md1 k1 o HJ Hoo)).
assert (HvG : v + 16 <= rg_s RG \/ rg_s RG + 4 * ASRC <= v).
{ destruct (Z_lt_le_dec (v + 15) (rg_s RG)) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_le_dec v (rg_s RG + 4 * ASRC)) as [Hlt2|Hge2]; [|right; lia].
  exfalso. destruct (Z_lt_le_dec v (rg_s RG)) as [Hlt3|Hge3].
  - destruct (dtk_blk_off_x ly1 S1 hp1 W1 m1 md1 v (AREC * hl_cap (hs_pending h1)) (rg_s RG) HAR Hvin
      ltac:(unfold AREC in *; lia)) as (_ & Hno). apply Hno. unfold ASRC; lia.
  - destruct (dtk_blk_off_x ly1 S1 hp1 W1 m1 md1 v (AREC * hl_cap (hs_pending h1)) v HAR Hvin
      ltac:(unfold AREC in *; lia)) as (_ & Hno). apply Hno. lia. }
assert (Hv3 : v mod 8 = 0).
{ destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hvin) as (H16 & _).
  apply Z.mod_divide in H16; [|lia]. destruct H16 as (q & Hq). rewrite Hq.
  replace (q * 16) with (0 + (2 * q) * 8) by lia. apply dt3_mod_addk; [lia | reflexivity]. }
pose proof (dt3_seat1 B RG HGSB cx W1 m1 regs1 (hl_n (hs_pending h1)) v len off p dn HR R23 Hj4 HSAlo HSAhi HspA0 HspB HspM
  HFR HW ltac:(lia) ltac:(lia) ltac:(unfold AREC in *; lia) Hv3 HvG Hlb ltac:(lia) Hpb Hmod8 Hdnr
  V12 V16 V24 V32 VP VL) as HS.
clear HvG.
remember (Eimg (Ereg regs1 (dt3_x1 (hl_n (hs_pending h1)) v len off p dn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (k : nat) (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ k r Hr)).
assert (EX : forall i, (i < 7)%nat ->
    ew E (32 + i) = nth i (dt3_x1 (hl_n (hs_pending h1)) v len off p dn) (Z_to_bv 64 0))
  by (intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ i)).
clear HE.
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E10 : ew E 10 = Z_to_bv 64 (re_buf e1 + re_used e1))
  by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact R10).
assert (E13 : ew E 13 = Z_to_bv 64 room) by (rewrite (EREG 13%nat 13%bv) by (first [lia | reflexivity]); exact R13).
assert (E19 : ew E 19 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 (dxSA cx)) by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21).
assert (E23 : ew E 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 v) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 off) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 p) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 dn) by exact (EX 6%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (HHA : dHA RG cx = rg_s RG + 96 * Z.of_nat (dxj cx)) by (unfold dHA, ASRC; reflexivity).
assert (HAb : 0 <= dHA RG cx /\ dHA RG cx + 96 < 2 ^ 47) by (rewrite HHA; unfold IMG_TOP, ASRC in *; lia).
assert (UB2 : U E dts_Bx2 = SHADOW_OFF) by (unfold dts_Bx2; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; unfold AREC in *; lia).
assert (SHA : forall E' mem md, ew E' 23 = Z_to_bv 64 (dHA RG cx) -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  ew E' 34 = Z_to_bv 64 v -> ARx ly1 S1 hp1 W1 mem md -> sh_ok SEGS dts_Bx2 dt3_SH E' (mrestrict (w_H W1) mem)).
{ intros E' mem md F23 F32 F34 HARm. unfold sh_ok, dt3_SH.
  assert (UB2' : U E' dts_Bx2 = SHADOW_OFF) by (unfold dts_Bx2; apply U_atom; [exact F32 | unfold SHADOW_OFF; lia]).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range SEGS (w_H W1) mem E' dts_Bx2 23%nat (rg_s RG) (4 * ASRC) (dHA RG cx) 0 96).
    + exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem md (rg_s RG) (4 * ASRC) HARm HGSZ).
    + exact UB2'.
    + apply (U_atom E' 23 (dHA RG cx) F23). lia.
    + rewrite HHA; lia.
    + rewrite HHA; unfold ASRC in *; lia.
    + intros x Hx. rewrite HHA in Hx. unfold SHADOW_OFF, IMG_TOP, ASRC in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W1) mem E' dts_Bx2 34%nat v (AREC * hl_cap (hs_pending h1)) v 0 16).
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem md v (AREC * hl_cap (hs_pending h1)) v
        (AREC * hl_cap (hs_pending h1)) HARm Hvin); [lia | lia].
    + exact UB2'.
    + apply (U_atom E' 34 v F34). unfold AREC in *; lia.
    + lia.
    + unfold AREC in *; lia.
    + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by (unfold AREC in *; lia).
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AREC in *. lia. }
pose proof (SHA E m1 md1 E23 E32 E34 HAR) as SHOK.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_slot)) with (Z_to_bv 64 (BASE + A_dr_slot)).
paj_run_to_tok_xR RUNTOG HS HJ SHOK dts_Bspan dt3_sh1; [dt3_awr_x Usp |].
rename HFr into FR1; rename HG0 into GR1; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msA end.
dt3_rs_x HS E HHA E8 E19 E23 E32 cx (12%bv : bv 5) 12.
paj_run_to_tok_xR RUNTOG HS HJ SHOK dts_Bspan dt3_sh2; [dt3_awr_x Usp |].
rename HFr into FR2; rename HG0 into GR2; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msB end.
dt3_rs_x HS E HHA E8 E19 E23 E32 cx (11%bv : bv 5) 24.
paj_run_to_tok_xR RUNTOG HS HJ SHOK dts_Bspan dt3_sh3; [dt3_awr_x Usp |].
rename HFr into FR3; rename HG0 into GR3; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msC end.
dt3_rs_x HS E HHA E8 E19 E23 E32 cx (11%bv : bv 5) 16.
paj_run_to_tok_xR RUNTOG HS HJ SHOK dts_Bspan dt3_sh4; [dt3_awr_x Usp |].
rename HFr into FR4; rename HG0 into GR4; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msD end.
dt3_rs_x HS E HHA E8 E19 E23 E32 cx (14%bv : bv 5) 32.
paj_run_tok_xR RUNG HS HJ SHOK dts_Bspan; [dt3_awr_x Usp |].
rename HFr into FR5; rename HG0 into GR5; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msE end.
assert (KALLE : forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x ->
  aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N.
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msD) (ms_mem msE) FR5 x Hx) by (dt3_nowrf_x Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msC) (ms_mem msD) FR4 x Hx) by (dt3_nowrf_x Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msB) (ms_mem msC) FR3 x Hx) by (dt3_nowrf_x Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msA) (ms_mem msB) FR2 x Hx) by (dt3_nowrf_x Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) m1 (ms_mem msA) FR1 x Hx) by (dt3_nowrf_x Usp N).
  reflexivity. }
assert (PRESE : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msE) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR5 (apresent_grows _ _ _ _ GR4
      (apresent_grows _ _ _ _ GR3 (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hp)))))).
assert (E13u : bv_unsigned (ew E 13) = room) by (rewrite E13; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = len) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = off) by (rewrite E36; apply unsigned_lit_small; lia).
assert (USUB : U E (SAlu ALU_ADD (SOff 35 0) (SMd M_MUL (SOff 36 0) (SLit (-1)))) = len - off)
  by (apply (dt3_U_sub B RG HGSB E 35 36 len off E35u E36u); lia).
assert (UPV : U E (SOff 37 0) = p) by (apply U_atom; [exact E37 | lia]).
assert (UOF : U E (SOff 36 0) = off) by (apply U_atom; [exact E36 | lia]).
assert (UP0 : U E (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) = off + p)
  by (apply (trap_U_add E (SOff 36 0) (SOff 37 0) off p UOF UPV); lia).
assert (TR1 : branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)))
  (sv_denot E (SOff 37 0)) = false)
  by (apply (trap_ptr_bltu E (SOff 37 0) (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) p (off + p) UPV UP0); lia).
eassert (CONT : forall (msF : machine_state) (mdF : Model),
  st_ok_pi SEGS VAL E ?[SSF] (restrict (w_H W1) msF) ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx)
    (dxmd cx) [] ly1 S1 hp1 W1 (ms_mem msF) mdF k1 ->
  sh_ok SEGS dts_Bx2 dt3_SH E (mrestrict (w_H W1) (ms_mem msF)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x -> aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x) ->
  (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x) ->
  YA0nH.SRrG SEGS R W1 (mkCfg msF mdF) (dPOST_xR B PST ARx MT RP RG R cx hp kr)).
2: {
psrr_branch_tok RUNG BRR HS SHOK dts_Bspan;
[ rewrite trap_br_ltu, USUB, (U_atom E 13 room E13 ltac:(lia)) in Hc; apply Z.ltb_lt in Hc;
  assert (Hdn2 : dn = len - off) by (clear - Hc Hdnh; unfold dt3_hide in Hdnh; lia);
  paj_run_to_tok_xR RUNTOG HS HJ SHOK dts_Bspan dt3_pc_n; [dt3_awr_x Usp |];
  rename HFr into FR6; rename HG0 into GR6; clear HF;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    dt3_reg_x HS (12%bv : bv 5) X12;
    assert (D12 : sv_denot E (SOff 38 0) = getr (ms_regs mx) 12%bv)
      by (rewrite X12, (den_atom0 E 38 dn E38) by lia;
          rewrite denot_lit_U, USUB, Hdn2; reflexivity) end
| rewrite trap_br_ltu, USUB, (U_atom E 13 room E13 ltac:(lia)) in Hc; apply Z.ltb_ge in Hc;
  assert (Hdn2 : dn = room) by (clear - Hc Hdnh; unfold dt3_hide in Hdnh; lia);
  paj_run_to_tok_xR RUNTOG HS HJ SHOK dts_Bspan dt3_pc_n; [dt3_awr_x Usp |];
  rename HFr into FR6; rename HG0 into GR6; clear HF;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    dt3_reg_x HS (12%bv : bv 5) X12;
    assert (D12 : sv_denot E (SOff 38 0) = getr (ms_regs mx) 12%bv)
      by (rewrite X12, (den_atom0 E 13 room E13) by lia; rewrite (den_atom0 E 38 dn E38) by lia;
          rewrite Hdn2; reflexivity) end ].
all: clear Hc Hdn2.
all: match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
all: pose proof (ast_ok_pi_set_reg_fp E _ _ (12%bv : bv 5) _ HS eq_refl D12) as HS';
     clear HS D12 X12; rename HS' into HS;
     cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS.
all: pose proof (st_ok_pi_facts_incl E _ _ _ _ HS (fun x Hx => Hx) (fun x Hx => Hx)) as HS'; clear HS;
     rename HS' into HS.
all: match type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
all: apply (CONT msF _ HS HJ SHOK);
  [ intros x Hx N; rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msE) (ms_mem msF) FR6 x Hx) by (dt3_nowrf_x Usp N);
    exact (KALLE x Hx N)
  | intros x Hp; exact (apresent_grows _ _ _ _ GR6 (PRESE x Hp)) ]. }
intros msF mdF HSc HJc SHc KALLF PRESF.
clear HS HJ SHOK KALLE PRESE FR1 FR2 FR3 FR4 FR5 GR1 GR2 GR3 GR4 GR5.
rename HSc into HS, HJc into HJ, SHc into SHOK.
paj_run_tok_xR RUNG HS HJ SHOK dts_Bspan; [dt3_awr_x Usp |].
rename HFr into FR7; rename HG0 into GR7; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msG end.
psrr_branch_tok RUNG BRR HS SHOK dts_Bspan; try (dt3_trap_x Hc TR1).
clear Hc.
paj_run_tok_xR RUNG HS HJ SHOK dts_Bspan; [dt3_awr_x Usp |].
rename HFr into FR8; rename HG0 into GR8; clear HF.
match type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into msM end.
assert (KALLM : forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x ->
  aview SEGS (w_H W1) (ms_mem msM) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N.
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msG) (ms_mem msM) FR8 x Hx) by (dt3_nowrf_x Usp N).
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem msF) (ms_mem msG) FR7 x Hx) by (dt3_nowrf_x Usp N).
  exact (KALLF x Hx N). }
assert (PRESM : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msM) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR8 (apresent_grows _ _ _ _ GR7 (PRESF x Hp)))).
clear FR7 FR8 GR7 GR8 KALLF PRESF.
subst dn room len p off v.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. dt3_reg_x HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp2 : spZ (ms_regs msM) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2; exact Usp).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARM.
assert (Hbne : re_cap e1 <> 0) by lia.
assert (Hrin : In (fst r0, Z.of_nat (length (snd r0)) + 1) (alist_blks (hs_pending h1))).
{ unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbn [app]. right. rewrite Erecs. cbn [map]. left.
  reflexivity. }
assert (Hvinl : In (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1)) (alist_blks (hs_pending h1))).
{ unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbn [app]. left. reflexivity. }
pose proof (dt3_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hr0in Hbin
  (dt3_pend_ne_x ly1 S1 hp1 W1 m1 md1 cx e1 h1 _ out1 _ HAR Hperm Hbne Hrin)) as Htap. rewrite RQC in Htap.
pose proof (dt3_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hvin Hbin
  (dt3_pend_ne_x ly1 S1 hp1 W1 m1 md1 cx e1 h1 _ out1 _ HAR Hperm Hbne Hvinl)) as Hvap. rewrite RQC in Hvap.
pose proof (dt3_blk_gs_x _ _ _ _ _ _ _ _ (dHA RG cx) 96 HAR Hbin ltac:(rewrite HHA; lia)
  ltac:(rewrite HHA; unfold ASRC; lia) ltac:(lia)) as Hbgs. rewrite RQC in Hbgs.
destruct HJ as (HSTK2 & HXO2 & (memS2 & HJi2 & HAG2) & HOUT2). rewrite !Z.add_0_r in HJi2.
eapply (YA0nH.SRrG_bind SEGS R R_trans);
[ eapply (aj_intrin_at_xR B PST ARx LAWS R_trans WLE_R OCpy (SIGMA WS_asan_memcpy) AMEMCPY W1 (ms_regs msM) (ms_mem msM)
    DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx) memS2 (dxmd cx) [] ly1 S1 hp1 _ k1
    (re_buf e1 + re_used e1) (hs_off h1 + fst r0) (dnum sg) (- DRAIN_FRAME) _ HJi2);
  [ rewrite Q10, E10; reflexivity
  | rewrite Q11, denot_lit_U, UP0; reflexivity
  | rewrite Q12, E38; reflexivity
  | clear - Hdnr; lia
  | clear - Hb4096 HUlen; lia
  | clear - Hbceil Hdnc HUlen C1; lia
  | rewrite Usp2; ring
  | rewrite HDF; reflexivity
  | rewrite HDF; lia
  | rewrite HDS, HDF; unfold ESTACK; lia
  | rewrite Q3, (EREG 3%nat 3%bv), R3 by (first [lia | reflexivity]); exact Hgp0
  | rewrite Q4, (EREG 4%nat 4%bv), R4 by (first [lia | reflexivity]); exact Htp0
  | exact Q1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; split;
    [ apply (dt3_buf_awr_x cx ly1 S1 hp1 W1 m1 md1 e1 h1 _ out1 a HAR HPERM0 Hperm Hbne);
        [ unfold ATABLE; clear - Hroom2 HUlen; lia | exact Hbin | clear - Ha Hdnc HUlen; lia ]
    | clear - Ha Hbceil Hdnc HUlen HspA HDS HDF; unfold ESTACK; lia ]
  | apply (dt3_amem_range_blk_x ly1 S1 hp1 W1 m1 md1 (re_buf e1) (re_cap e1));
      [exact HAR | exact Hbin | clear - HUlen; lia | rewrite RQC; clear - Hdnc HUlen; lia]
  | eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (re_buf e1) (re_cap e1));
      [exact HARM | exact Hbin | clear - HUlen; lia | rewrite RQC; clear - Hdnc HUlen; lia]
  | intros Hpos; eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (re_buf e1) (re_cap e1));
      [exact HARM | exact Hbin | clear - HUlen; lia | rewrite RQC; clear - Hdnc HUlen; lia | exact Hpos]
  | split; [clear - Hoff0 Hs4096; lia|];
    split; [clear - Hsceil Hdnl HoffL Hoff0 Rq0 C1; lia|];
    split; [|split; [clear - Htap Hdnl Hdnc Hoff0 HoffL HUlen Rq0 Hdnr; unfold dt3_apart in Htap; lia|]];
    [ intros a Ha; split; [|rewrite Usp2; clear - Ha Hsceil Hdnl Hoff0 HoffL Rq0 HspA HDS HDF; unfold ESTACK; lia];
      rewrite KALLM by (clear - Ha Hsceil Hdnl Hoff0 HoffL Hs4096 Rq0 HspA HDS HDF C1; unfold dt3_wfr; lia);
      replace a with (fst r0 + Z.of_nat (Z.to_nat (a - fst r0))) by (clear - Ha Hoff0; lia);
      rewrite (dt3_garr8_aview W1 m1 _ _ _ Hr0g)
        by (rewrite dt3_bzs_len, length_app; cbn [length]; clear - Ha HoffL Hdnl Hoff0; lia);
      discriminate
    | split; [apply (dt3_amem_range_blk_x ly1 S1 hp1 W1 m1 md1 (fst r0) (Z.of_nat (length (snd r0)) + 1));
        [exact HAR | exact Hr0in | clear - Hoff0; lia | clear - Hdnl HoffL Hoff0 Rq0; lia]|];
      split; [eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (fst r0)
        (Z.of_nat (length (snd r0)) + 1)); [exact HARM | exact Hr0in | clear - Hoff0; lia
        | clear - Hdnl HoffL Hoff0 Rq0; lia]|];
      intros Hpos; eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem msM) _ (fst r0)
        (Z.of_nat (length (snd r0)) + 1)); [exact HARM | exact Hr0in | clear - Hoff0; lia
        | clear - Hdnl HoffL Hoff0 Rq0; lia | exact Hpos] ] ]
| ].
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3i & HP3 & Hd10b & Hcpy & Hfr3 & Hpres3).
jafter_call_keep_pi HS 39%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  all: first
    [ apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 2 (dsp0 cx - DRAIN_FRAME)); [exact Usp | | exact Hpres3];
      intros a Ha; apply Hfr3; clear - Ha Hbceil Hdnc HUlen HspA HspB HDS HDF C1; unfold ESTACK; lia
    | apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 23 (dHA RG cx)); [exact U23 | | exact Hpres3];
      intros a Ha; apply Hfr3; clear - Ha HAb Hbgs Hdnc HUlen HspA HDS HDF HHA G1 G2 C1 Hj4;
      unfold dt3_apart, ESTACK, ASRC, IMG_TOP in *; lia
    | apply (region_kept_aview E (w_H W1) (ms_mem msM) mem3 34 (hl_v (hs_pending h1))); [exact U34 | | exact Hpres3];
      intros a Ha; apply Hfr3; clear - Ha Hvap Hv4096 Hvceil Rqv Hcpv Hdnc HUlen HspA HDS HDF C1;
      unfold dt3_apart, AREC, ESTACK in *; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 39 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 39)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDa by lia; exact Usp).
pose proof (proj1 HJ3i) as HAR3.
assert (SHOK3 : sh_ok SEGS dts_Bx2 dt3_SH Ea (mrestrict (w_H W1) mem3))
  by (apply (SHA Ea mem3 md3); [rewrite OLDa by lia; exact E23 | rewrite OLDa by lia; exact E32
      | rewrite OLDa by lia; exact E34 | exact HAR3]).
assert (HJ3 : @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx)
  (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mem3 md3 k1)
  by (apply (ajournal_gx_pack_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx)
    (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mem3 md3 k1 memS2);
    [exact HSTK2 | lia | rewrite !Z.add_0_r; exact HJ3i | exact HAG2 | apply out_none]).
clear HJ3i HAG2 HOUT2.
assert (A36 : U Ea (SOff 36 0) = hs_off h1) by (apply U_atom; [rewrite OLDa by lia; exact E36 | lia]).
assert (A37 : U Ea (SOff 37 0) = fst r0) by (apply U_atom; [rewrite OLDa by lia; exact E37 | lia]).
paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 dts_Bspan dt3_pc_drb; [dt3_awr_x UspA |].
rename HFr into FR10; rename HG0 into GR10; clear HF.
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msR end.
assert (K10 : forall x, 0 <= x < 2 ^ 64 -> ~ dt3_wfr cx x ->
  aview SEGS (w_H W1) (ms_mem msR) x = aview SEGS (w_H W1) mem3 x).
{ intros x Hx N. rewrite (aview_kept_out _ _ (w_H W1) mem3 (ms_mem msR) FR10 x Hx) by (dt3_nowrf_x UspA N).
  reflexivity. }
assert (PRESR : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msR) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR10 (Hpres3 _ (PRESM x Hp)))).
set (data := firstn (Z.to_nat (dnum sg)) (skipn (Z.to_nat (hs_off h1)) (snd r0))).
assert (Hdlen : length data = Z.to_nat (dnum sg))
  by (unfold data; rewrite length_firstn, length_skipn; clear - Hdnl Hoff0 HoffL Hdnr; lia).
assert (Hdlj : (length data <= length (re_junk e1))%nat) by (rewrite Hdlen; clear - Hjl Hdnc Hdnr; lia).
assert (CPY : forall i, (i < length data)%nat ->
  aview SEGS (w_H W1) (ms_mem msR) (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)).
{ intros i Hi. rewrite Hdlen in Hi.
  assert (Hi' : 0 <= Z.of_nat i < dnum sg) by (clear - Hi Hdnr; lia).
  rewrite K10 by (clear - Hi' Hb4096 Hbceil Hdnc HUlen HspA HDS HDF C1; unfold dt3_wfr; lia).
  pose proof (Hcpy (Z.of_nat i) Hi') as Hc. cbv iota in Hc. rewrite Hc.
  rewrite KALLM by (clear - Hi' Hsceil Hdnl Hoff0 HoffL Hs4096 Rq0 HspA HDS HDF C1; unfold dt3_wfr; lia).
  replace (hs_off h1 + fst r0 + Z.of_nat i) with (fst r0 + Z.of_nat (Z.to_nat (hs_off h1) + i))
    by (clear - Hoff0; lia).
  rewrite (dt3_garr8_aview W1 m1 _ _ _ Hr0g)
    by (rewrite dt3_bzs_len, length_app; cbn [length]; clear - Hi HoffL Hdnl Hoff0 Hdnr; lia).
  f_equal. unfold data. apply (dt3_nth_data B RG HGSB); clear - Hi HoffL Hdnl Hoff0 Hdnr; lia. }
assert (KEEP : forall x, 0 <= x < 2 ^ 64 ->
  ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
  ~ (dsp0 cx - DRAIN_STK_x <= x < dsp0 cx) ->
  aview SEGS (w_H W1) (ms_mem msR) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. rewrite Hdlen in N1.
  assert (NW : ~ dt3_wfr cx x) by (clear - N2 HDS HDF; unfold dt3_wfr; lia).
  rewrite (K10 x Hx NW).
  rewrite (Hfr3 x Hx ltac:(clear - N1 Hdnr; lia) ltac:(clear - N2 HDS HDF; unfold ESTACK; lia)).
  exact (KALLM x Hx NW). }
assert (HFRR : dr_frame RG cx W1 (ms_mem msR)).
{ apply (dt3_frame_kept B RG HGSB cx W1 m1 (ms_mem msR) HFR HspA0 HspB).
  intros x Hx N. assert (Hx64 : 0 <= x < 2 ^ 64) by (clear - Hx HspA HspB HDS HDF C1; lia).
  rewrite (K10 x Hx64 N).
  rewrite (Hfr3 x Hx64 ltac:(clear - Hx Hbceil Hdnc HUlen HspA HDS HDF; lia)
    ltac:(clear - Hx HDF; unfold ESTACK; lia)).
  exact (KALLM x Hx64 N). }
pose proof (dt3_dmem_drb_xR cx hp kr sg ly1 S1 hp1 W1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 (ms_mem msR) _ data
  HB HMEM HJ3 Hcpos Hdlj KEEP PRESR CPY HFRR) as HMEMF.
assert (Hstr : dstrict sg).
{ intros r rs Hrs. rewrite Hpend0 in Hrs. injection Hrs as <- _. rewrite dt3_bzs_len, <- Loff. clear - HoffL. lia. }
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS24. cbn [ms_mem restrict] in RS24.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS96. cbn [ms_mem restrict] in RS96.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS112. cbn [ms_mem restrict] in RS112.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS160. cbn [ms_mem restrict] in RS160.
pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RS168. cbn [ms_mem restrict] in RS168.
pose proof (st_ok_pi_region_nth _ _ _ 5 _ HS eq_refl) as RS192. cbn [ms_mem restrict] in RS192.
assert (F8 : ew Ea 8 = Z_to_bv 64 (rg_s RG)) by (rewrite OLDa by lia; exact E8).
assert (F19 : ew Ea 19 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx))) by (rewrite OLDa by lia; exact E19).
assert (F23 : ew Ea 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite OLDa by lia; exact E23).
assert (F23g : ew Ea 23 = Z_to_bv 64 (rg_s RG + 96 * Z.of_nat (dxj cx))) by (rewrite <- HHA; exact F23).
assert (F32 : ew Ea 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; exact E32).
assert (F37 : ew Ea 37 = Z_to_bv 64 (fst r0)) by (rewrite OLDa by lia; exact E37).
assert (F38 : ew Ea 38 = Z_to_bv 64 (dnum sg)) by (rewrite OLDa by lia; exact E38).
assert (UP0a : U Ea (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) = hs_off h1 + fst r0)
  by (apply (trap_U_add Ea (SOff 36 0) (SOff 37 0) (hs_off h1) (fst r0) A36 A37); lia).
assert (R64 : forall z, 0 <= z < 2 ^ 64 -> 0 <= z < 2 ^ (8 * Z.of_N 8)) by (intros z Hz; exact Hz).
assert (V24F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 24) 8 (dHA RG cx + 56)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 24 32 24 32 24 8%N (SOff 23 56) (dHA RG cx + 56)
      RS24 UspA);
    [left; reflexivity | apply (den_atom Ea 23 (dHA RG cx) 56 F23); lia | apply R64; lia | lia]. }
assert (V96F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 96) 8 (dHA RG cx + 16)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 96 104 96 104 96 8%N (SOff 23 16) (dHA RG cx + 16)
      RS96 UspA);
    [left; reflexivity | apply (den_atom Ea 23 (dHA RG cx) 16 F23); lia | apply R64; lia | lia]. }
assert (V160F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 160) 8 (dHA RG cx + 64)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 160 168 160 168 160 8%N (SOff 23 64) (dHA RG cx + 64)
      RS160 UspA);
    [left; reflexivity | apply (den_atom Ea 23 (dHA RG cx) 64 F23); lia | apply R64; lia | lia]. }
assert (V112F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 112) 8 (shadow_addr (dHA RG cx + 16))).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 112 120 112 120 112 8%N
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 16) (SLit 3)) (SOff 32 0)) (shadow_addr (dHA RG cx + 16))
      RS112 UspA);
    [left; reflexivity | apply (dt3_den_shA B RG Ea 23 (dHA RG cx) 16 F23 F32); lia | apply R64, (dt3_sh_range B RG); lia | lia]. }
assert (V168F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 168) 8 (shadow_addr (dHA RG cx + 32))).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 168 176 168 176 168 8%N
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 32) (SLit 3)) (SOff 32 0)) (shadow_addr (dHA RG cx + 32))
      RS168 UspA);
    [left; reflexivity | apply (dt3_den_shA B RG Ea 23 (dHA RG cx) 32 F23 F32); lia | apply R64, (dt3_sh_range B RG); lia | lia]. }
assert (V192F : val_mem SEGS (arm W1 (ms_mem msR)) (dsp0 cx - DRAIN_FRAME + 192) 8 (dnum sg)).
{ apply (field_of_region Ea _ 2%nat (dsp0 cx - DRAIN_FRAME) _ 192 200 192 200 192 8%N (SOff 38 0) (dnum sg)
      RS192 UspA);
    [left; reflexivity | apply (den_atom0 Ea 38 (dnum sg) F38); lia | apply R64; lia | lia]. }
clear RS24 RS96 RS112 RS160 RS168 RS192.
pmkst HS.
prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3. prreg HS (4%bv : bv 5) Y4.
prreg HS (8%bv : bv 5) Y8. prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18. prreg HS (23%bv : bv 5) Y23.
prreg HS (15%bv : bv 5) Y15. prreg HS (21%bv : bv 5) Y21. prreg HS (6%bv : bv 5) Y6. prreg HS (20%bv : bv 5) Y20.
dt3_reg_x HS (27%bv : bv 5) Y27. dt3_reg_x HS (19%bv : bv 5) Y19. dt3_reg_x HS (24%bv : bv 5) Y24.
dt3_reg_x HS (16%bv : bv 5) Y16. dt3_reg_x HS (17%bv : bv 5) Y17. dt3_reg_x HS (22%bv : bv 5) Y22.
rewrite ?OLDa in Y2, Y3, Y4, Y8, Y9, Y18, Y23, Y15, Y21, Y6 by lia.
assert (RP0 : forall r : bv 5, getr (ms_regs msR) r = sv_denot Ea (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) ->
  getr (ms_regs msR) r = w64 (fst r0 + drain_b_c.ds_off sg + Z.of_nat 0)).
{ intros r Hr. rewrite Hr, denot_lit_U, UP0a. unfold w64. f_equal. rewrite <- Loff. lia. }
assert (RSH : forall (r : bv 5) c, 0 <= c <= 56 ->
  getr (ms_regs msR) r = sv_denot Ea (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 c) (SLit 3)) (SOff 19 0)) ->
  getr (ms_regs msR) r = w64 (shadow_addr (dHA RG cx + c))).
{ intros r c Hc Hr. rewrite Hr.
  rewrite (dt3_den_resh B RG HGSB Ea (rg_s RG) (Z.of_nat (dxj cx)) c F8 F19 F23g F32) by (try rewrite <- HHA; lia).
  exact (dt3_den_shA B RG Ea 23 (dHA RG cx) c F23 F32 ltac:(lia) ltac:(lia)). }
match goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdR := mdx) in * end.
apply (Krb W1). unfold DRB_xR.
exists (ms_regs msR), ly1, S1, hp1, (ms_mem msR), mdR, k1, (dt3_junk e1 (data ++ skipn (length data) (re_junk e1))),
  h1, out1, ev1, LB1, spent, jb, aa, (drain_b_c.da_ev aa), (drain_b_c.da_erecs aa), tl,
  (fst r0 + drain_b_c.ds_off sg), r0, rs0.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ; rewrite Y2; exact Usp|].
split; [rewrite Y3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
split; [rewrite Y4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
split; [rewrite Y8; exact E8|].
split; [rewrite Y9, (EREG 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
split; [rewrite Y18, (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
split; [rewrite Y23; exact E23|].
split; [rewrite Y15; exact E38|].
split; [rewrite Y21, E38; change (Z.of_nat 0) with 0; rewrite Z.sub_0_r; reflexivity|].
split; [rewrite (RP0 _ Y27); change (Z.of_nat 0) with 0; rewrite Z.add_0_r; reflexivity|].
split; [exact (RP0 _ Y19)|].
split; [exact (RP0 _ Y24)|].
split; [rewrite Y6; exact E37|].
split; [rewrite Y20; reflexivity|].
split; [exact (RSH _ 40 ltac:(lia) Y16)|].
split; [exact (RSH _ 48 ltac:(lia) Y17)|].
split; [exact (RSH _ 56 ltac:(lia) Y22)|].
split; [exact HFRR|].
split; [exact V24F|]. split; [exact V96F|]. split; [exact V160F|].
split; [exact V112F|]. split; [exact V168F|]. split; [exact V192F|].
split; [exact Erecs|].
split; [reflexivity|].
split; [unfold dinband; clear - Hs4096 Hsceil Rq0 Hmod8 C1; unfold DCEIL; lia|].
split; [rewrite <- Loff; clear - Hoff0; lia|].
split; [clear - Hdnr; lia|].
split; [clear - Hdnr; lia|].
split.
{ cbn [dt3_junk re_junk].
  rewrite firstn_app, Hdlen, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite Hdlen; apply le_n).
  unfold data, ddata. rewrite Hdhead, <- Loff, dt3_skipn_bzs, dt3_firstn_bzs. reflexivity. }
split; [exact HMEMF|].
split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hinb|]. split; [exact HSAME|].
split; [exact Lcap|]. split; [exact Lu|]. split; [exact Lsk|]. split; [exact LH|]. split; [exact Lka|].
split; [exact Hei0|]. split; [exact Lpend|]. split; [exact Loff|].
split; [rewrite firstn_O, dtm_feed_nil; exact Lst|].
split; [rewrite firstn_O, dtm_lines_nil; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact Len|].
split; [rewrite firstn_O, dtm_lines_nil, dtm_pcapm_nil; exact Lecap|].
split; [rewrite firstn_O, app_nil_r; exact HHIST|].
split.
{ unfold RSTART. split; [exact (proj1 (proj2 HHIST))|]. split; [exact HJ1|]. split; [exact Hroom|].
  split; [exact Lwf|]. split; [exact Hstr|]. split; [exact Hei | exact Hpne]. }
split; [eapply (dtm_pfut0 B RG HGSB); eassumption | exact Hbud].
Qed.

Theorem dr_toptail_xR : dr_toptail_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx hp kr sg D W1 c1 HB HDT KEI KEND KRB.
destruct (drain_b_c.ds_eintr sg) eqn:EI.
- exact (dt1_eintr_xR cx hp kr sg D W1 c1 HB HDT EI (KEI eq_refl)).
- destruct (drain_b_c.ds_pend sg) as [|r0 rs0] eqn:EP.
  + exact (dt2_end_xR cx hp kr sg D W1 c1 HB HDT EI EP KEND).
  + refine (dt3_data_xR cx hp kr sg D W1 c1 HB HDT EI _ KRB). rewrite EP. discriminate.
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R; the statements are the strict ones, checked by conversion). ---- *)
Lemma dtm_frame_wr_x : forall cx hp ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 o,
  @ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 m1 md1 k1 ->
  0 <= o < DRAIN_FRAME -> writable_at SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + o).
Proof. exact (dtm_frame_wr_xR (@wle SEGS)). Qed.

Lemma dtk_DMEM_kept_x : forall cx hp ly1 S1 hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof. exact (dtk_DMEM_kept_xR (@wle SEGS)). Qed.

Lemma dt1_dmem_x : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF,
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dHA RG cx + 12 <= x < dHA RG cx + 16) ->
   ~ (as_errno B <= x < as_errno B + 4) ->
   ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
asrc_at B ly1 S1 W1 mF (dHA RG cx) (dtk_set_eintr h1) ->
val_mem SEGS (arm W1 mF) (as_errno B) 4 4 ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 mF mdF k1 e1 (dtk_set_eintr h1) (dclr sg) out1 4 sent LB1.
Proof. exact (dt1_dmem_xR (@wle SEGS)). Qed.

Lemma dt1_eintr_x : forall cx hp kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx hp kr -> DT2_x B PST ARx MT RP MMAX RG cx hp kr sg D W1 c1 ->
drain_b_c.ds_eintr sg = true ->
(forall W2 c2, DI_x B PST ARx MT RP MMAX RG cx hp kr (dclr sg) D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx hp kr).
Proof. exact (dt1_eintr_xR (@wle SEGS) (wle_trans SEGS) (fun _ _ H => H)). Qed.

Lemma dt2_end_x : forall cx hp kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx hp kr -> DT2_x B PST ARx MT RP MMAX RG cx hp kr sg D W1 c1 ->
drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg = [] ->
(forall W2 c2, DEND_x B PST ARx MT RP MMAX RG cx hp kr sg D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx hp kr).
Proof. exact (dt2_end_xR (@wle SEGS)). Qed.

Lemma dt3_dmem_drb_x : forall cx hp kr sg ly1 S1 hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 sent LB1 mF mdF (data : list byte),
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 hp1 W1 mF mdF k1 ->
0 < re_cap e1 -> (length data <= length (re_junk e1))%nat ->
(forall x, 0 <= x < 2 ^ 64 ->
   ~ (re_buf e1 + re_used e1 <= x < re_buf e1 + re_used e1 + Z.of_nat (length data)) ->
   ~ (dsp0 cx - DRAIN_STK_x <= x < dsp0 cx) ->
   aview SEGS (w_H W1) mF x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mF x) ->
(forall i, (i < length data)%nat ->
   aview SEGS (w_H W1) mF (re_buf e1 + re_used e1 + Z.of_nat i) = Some (nth i (bzs data) 0)) ->
dr_frame RG cx W1 mF ->
DMEM_x B PST ARx RG cx hp ly1 S1 hp1 W1 mF mdF k1 (dt3_junk e1 (data ++ skipn (length data) (re_junk e1))) h1 sg out1 ev1 sent LB1.
Proof. exact (dt3_dmem_drb_xR (@wle SEGS)). Qed.

Lemma dt3_data_x : forall cx hp kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx hp kr -> DT2_x B PST ARx MT RP MMAX RG cx hp kr sg D W1 c1 ->
drain_b_c.ds_eintr sg = false -> drain_b_c.ds_pend sg <> [] ->
(forall W2 c2, DRB_x B PST ARx MT RP MMAX RG cx hp kr sg D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx hp kr).
Proof. exact (dt3_data_xR (@wle SEGS) (wle_trans SEGS) (fun _ _ H => H)). Qed.

Theorem dr_toptail_x : dr_toptail_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dr_toptail_xR (@wle SEGS) (wle_trans SEGS) (fun _ _ H => H)). Qed.

End cx.
End b.
End a.
