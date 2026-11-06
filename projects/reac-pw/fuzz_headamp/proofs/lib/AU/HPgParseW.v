(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v at afaa3cb55c1 (the engine plumbing
   of a segment of a parse walk: entry state, run / branch / exit tactics, the frame temporaries as region chunks), for
   reac_headamp_prop_parse_result's pair loop on reac-pw/fuzz_headamp's ASan + UBSan image B, its two segments WALK
   and ADV of lib/AU/HPgParseCut.v; the arithmetic both images share is lib/A/HPgParseGWalk.v's; the entry states,
   the inner cuts WLB / WRET, the exits, the strncmp call inside the frame hole and the walks below are new. *)
(* reac_headamp_prop_parse_result 0x849ac of fuzz_headamp.asan-ubsan (pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94), segments WALK 0x84cb4 and ADV 0x84edc of
   lib/AU/HPgParseCut.v: segWALK_ok : segWALK_stmt B MT and segADV_ok : segADV_stmt B MT. Proves no function
   (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase HPgParseGWalk.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgParseCut.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseGKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= image B's own engine forms ======================================= *)
(* (the forms both images share are lib/A/HPgParseGWalk.v's hgw_U_* lemmas) *)
(* srli a0,a2,0x14 of the u32 CS *)
Lemma pbW_U_srl20 : forall E n v, U E (SOff n 0) = v -> 0 <= v < 2 ^ 32 ->
U E (SAlu ALU_SRL (SOff n 0) (SLit 20)) = v / 2 ^ 20.
Proof.
intros E n v Hv Hr. rewrite U_SAlu, Hv, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 20) 63) with 20.
rewrite Z.shiftr_div_pow2 by lia.
assert (0 <= v / 2 ^ 20 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply zcanon_id. unfold M64. lia.
Qed.

(* a1 = s7 + 8; addiw a0,a2,-1; add a0,a1,a0: the String child's last body byte s7 + 8 + CS - 1 *)
Lemma pbW_U_last : forall E n m s cs, U E (SOff n 0) = s -> U E (SOff m 0) = cs -> 0 <= s -> 1 <= cs < 2 ^ 31 ->
s + 8 + cs - 1 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n 8) (SAluw ALU_ADD (SOff m 0) (SLit (-1)))) = s + 8 + cs - 1.
Proof.
intros E n m s cs Hs Hc Hs0 Hcs Hlt.
assert (Hw : U E (SAluw ALU_ADD (SOff m 0) (SLit (-1))) = cs - 1).
{ rewrite U_of_S, S_SAluw, Hc, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
  change ((-1) mod 2 ^ 64) with 18446744073709551615. change (18446744073709551615 mod 2 ^ 32) with 4294967295.
  rewrite (Z.mod_small cs) by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  change (bv_modulus 64) with (2 ^ 64).
  replace (cs + 4294967295 + 2 ^ 31) with ((cs - 1 + 2 ^ 31) + 1 * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (cs - 1 + 2 ^ 31) (2 ^ 32)) by lia.
  replace (cs - 1 + 2 ^ 31 - 2 ^ 31) with (cs - 1) by lia. apply Z.mod_small. lia. }
rewrite U_SAlu, (hgw_U_off E n s 8 Hs ltac:(lia)), Hw. cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* snez a2,a1 (folded to 1); seqz a3,a0; xor a2,a2,a3: 1 when a0 <> 0 *)
Lemma pbW_U_nz : forall E e, U E e <> 0 ->
U E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU e (SLit 1))) = 1.
Proof.
intros E e He. pose proof (U_range E e) as R.
rewrite !U_SAlu, !U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
rewrite (proj2 (Z.ltb_ge (U E e) 1)) by lia. reflexivity.
Qed.

(* snez a0,a0; addi a0,a0,-1; and s8,a0,a1: a1 when the byte b is 0, else 0 *)
Lemma pbW_U_mask : forall E nb na b p, U E (SOff nb 0) = b -> U E (SOff na 0) = p -> 0 <= b < 256 ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff nb 0)) (SLit (-1))) (SOff na 0)) =
if b =? 0 then p else 0.
Proof.
intros E nb na b p Hb Hp Hr. pose proof (U_range E (SOff na 0)) as R. rewrite Hp in R. unfold M64 in R.
rewrite !U_SAlu, !U_SLit, Hb, Hp. cbn [zalu_raw]. change (zcanon 0) with 0.
destruct (Z.eqb_spec b 0) as [->|E0].
- replace (zcanon (zcanon (if 0 <? 0 then 1 else 0) + zcanon (-1))) with (Z.ones 64) by reflexivity.
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
- rewrite (proj2 (Z.ltb_lt 0 b)) by lia.
  replace (zcanon (zcanon 1 + zcanon (-1))) with 0 by reflexivity. rewrite Z.land_0_l. reflexivity.
Qed.

(* ======================================= the model at the pair loop's tests ======================================= *)
Local Notation pctx := (@hp_ctx rsegs).

(* case A: the child's header lies in the Struct body *)
Lemma pbW_inside_A : forall (x : pctx) r cc, r + 16 <= cc -> cc mod 8 = 0 -> cc + 8 <= r + 16 + hp_vs x r ->
Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = (Spa.u32_at (hx_bs x) cc <=? r + 8 + hp_vs x r - cc).
Proof.
intros x r cc H1 H2 H3. rewrite hgw_inside by lia.
rewrite (proj2 (Z.leb_le (cc - (r + 16)) (hp_vs x r - 8))) by lia. reflexivity.
Qed.

(* case B: it does not *)
Lemma pbW_out_B : forall (x : pctx) r cc, r + 16 <= cc -> cc mod 8 = 0 -> r + 16 + hp_vs x r < cc + 8 ->
Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false.
Proof.
intros x r cc H1 H2 H3. destruct (Z_lt_le_dec (hp_vs x r) 8) as [L|L]; [apply hgw_inside_small; exact L|].
rewrite hgw_inside by lia. rewrite (proj2 (Z.leb_gt (cc - (r + 16)) (hp_vs x r - 8))) by lia. reflexivity.
Qed.

(* the key slot after a child that fails one of spa_pod_get_string's first three tests *)
Lemma pbW_ko_none : forall (x : pctx) cc, 0 <= cc ->
(2 ^ 20 <= Spa.u32_at (hx_bs x) cc \/ Spa.u32_at (hx_bs x) cc = 0 \/ Spa.u32_at (hx_bs x) (cc + 4) <> 8) ->
hgw_ko x cc = None.
Proof.
intros x cc H0 H. unfold hgw_ko. rewrite (hgw_gs (hx_bs x) cc H0).
destruct H as [H|[H|H]].
- rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
- rewrite H. destruct (0 <? 2 ^ 20), (Spa.u32_at (hx_bs x) (cc + 4) =? 8); reflexivity.
- rewrite (proj2 (Z.eqb_neq _ _) H). rewrite andb_false_r. reflexivity.
Qed.

(* the key register after a String-sized child: the child's text when its last body byte is NUL *)
Lemma pbW_keyv_lb : forall (x : pctx) cc, 0 <= cc ->
1 <= Spa.u32_at (hx_bs x) cc < 2 ^ 20 -> Spa.u32_at (hx_bs x) (cc + 4) = 8 ->
hp_keyv x (hgw_ko x cc) =
if bv_unsigned (nth (Z.to_nat (cc + 8 + Spa.u32_at (hx_bs x) cc - 1)) (hx_bs x) Cursor.NUL) =? 0
then hx_P x + cc + 8 else 0.
Proof.
intros x cc H0 H1 H2. rewrite hgw_keyv_ko, (hgw_gs (hx_bs x) cc H0).
rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite H2, (proj2 (Z.leb_le 1 _)) by lia. cbn [Z.eqb andb].
destruct (_ =? 0); reflexivity.
Qed.

(* ======================================= the two cuts inside WALK ======================================= *)
(* WLB 0x84d54: a String-sized child (size in [1, 2^20), type 8) with the key slot empty; a0 = its last body byte's
   address s7 + 8 + CS - 1 (the engine cannot form that byte's shadow address from s7: the cut makes a0 an atom),
   a1 = s7 + 8, a7 = the shadow address of s7.
   WRET 0x84d98: strncmp's return for the pending key ck; a0 = 0 exactly when the key has the prefix. *)
Definition PC_WLB : Z := 0x84d54.
Definition PC_WRET : Z := 0x84d98.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Definition WLB_at (x : pctx) (r cc : Z) (n : nat) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_walk x r cc (S n) None cl keys rf /\
hp_child_in x r cc /\ 1 <= Spa.u32_at (hx_bs x) cc < 2 ^ 20 /\ Spa.u32_at (hx_bs x) (cc + 4) = 8 /\
pb_loop x r cl rf regs mem /\ pb_a46 x r regs /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 0 /\ getr regs 25 = w64 keys /\
getr regs 17 = w64 (shadow_addr (hx_P x + cc)) /\
getr regs 10 = w64 (hx_P x + cc + 8 + Spa.u32_at (hx_bs x) cc - 1) /\ getr regs 11 = w64 (hx_P x + cc + 8).

Definition WLB_ok (x : pctx) (r cc : Z) (n : nat) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md, WLB_at x r cc n cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_WLB regs mem md) (PPOST B MT x).

Definition WRET_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\
hp_m_walk x r cc (S n) (Some ck) cl keys rf /\ hp_child_in x r cc /\ pb_loop x r cl rf regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (hx_P x + ck + 8) /\ getr regs 25 = w64 keys /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) /\
(getr regs 10 = w64 0 <-> Headamp.ha_prefix (hp_kstr x ck) = true).

Definition WRET_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md, WRET_at x r cc n ck cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_WRET regs mem md) (PPOST B MT x).

(* ======================================= the strncmp call (0x84d94 jal 0x41c24) ======================================= *)
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d812c.
Hypothesis STRNCMP : forall F fc, hd_astrncmp_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRNCMP.

Lemma pbW_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac pbW_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.

(* the cut WRET from strncmp's post *)
Lemma pbW_ret_at : forall (x : pctx) r cc n ck cl keys rf F fc regsT memT regs2 mem2 md2,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2 -> hp_fxw F fc ->
hp_m_walk x r cc (S n) (Some ck) cl keys rf -> hp_child_in x r cc -> pb_loop x r cl rf regsT memT ->
getr regsT 23 = w64 (hx_P x + cc) -> getr regsT 24 = w64 (hx_P x + ck + 8) -> getr regsT 25 = w64 keys ->
val_mem rsegs (hx_rd x memT) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) ->
aregs_preserved regsT regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 2 * ESTACK <= a < hx_spa x) ->
 aview rsegs (w_H (hx_W x)) mem2 a = aview rsegs (w_H (hx_W x)) memT a) ->
(getr regs2 10 = w64 0 <-> Headamp.ha_prefix (hp_kstr x ck) = true) ->
WRET_at x r cc n ck cl keys rf F fc regs2 mem2 md2.
Proof.
intros x r cc n ck cl keys rf F fc regsT memT regs2 mem2 md2 Hc HC Hfx HW Hin (L20 & L21 & L22 & L16 & L32 & L40)
  R23 R24 R25 H48 HP HK H10.
pose proof (hk_stack B x Hc) as HS. pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
assert (KV : forall o (k : nat) v, 0 <= o <= 0x40 -> (k <= 8)%nat ->
  val_mem rsegs (hx_rd x memT) (hx_spa x + o) k v -> val_mem rsegs (hx_rd x mem2) (hx_spa x + o) k v).
{ intros o k v Ho Hk Hv. apply (val_mem_kept rsegs (w_H (hx_W x)) (w_H (hx_W x)) memT mem2); [|exact Hv].
  intros j Hj. apply HK; lia. }
split; [exact HC|]. split; [exact Hfx|]. split; [exact HW|]. split; [exact Hin|]. split.
{ unfold pb_loop. rewrite (pbW_pres regsT regs2 20%bv HP ltac:(pbW_acs)), (pbW_pres regsT regs2 21%bv HP ltac:(pbW_acs)),
    (pbW_pres regsT regs2 22%bv HP ltac:(pbW_acs)).
  split; [exact L20|]. split; [exact L21|]. split; [exact L22|].
  split; [exact (KV 16 8%nat _ ltac:(lia) ltac:(lia) L16)|]. split; [exact (KV 32 8%nat _ ltac:(lia) ltac:(lia) L32)|].
  exact (KV 40 8%nat _ ltac:(lia) ltac:(lia) L40). }
rewrite (pbW_pres regsT regs2 23%bv HP ltac:(pbW_acs)), (pbW_pres regsT regs2 24%bv HP ltac:(pbW_acs)),
  (pbW_pres regsT regs2 25%bv HP ltac:(pbW_acs)).
split; [exact R23|]. split; [exact R24|]. split; [exact R25|].
split; [exact (KV 48 8%nat _ ltac:(lia) ltac:(lia) H48) | exact H10].
Qed.

Lemma pbW_call : forall (x : pctx) r cc n ck cl keys rf F fc regsT memT mdT,
call_ok B x ->
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regsT memT mdT -> hp_fxw F fc ->
hp_m_walk x r cc (S n) (Some ck) cl keys rf -> hp_child_in x r cc -> pb_loop x r cl rf regsT memT ->
getr regsT 23 = w64 (hx_P x + cc) -> getr regsT 24 = w64 (hx_P x + ck + 8) -> getr regsT 25 = w64 keys ->
getr regsT 10 = w64 (hx_P x + ck + 8) -> getr regsT 11 = w64 0x214a0 -> getr regsT 12 = w64 13 ->
getr regsT 1 = w64 PC_WRET ->
val_mem rsegs (hx_rd x memT) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) ->
WRET_ok x r cc n ck cl keys rf ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs B_TRAMP_STRNCMP regsT memT mdT) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf F fc regsT memT mdT Hc HC Hfx HW Hin HL R23 R24 R25 R10 R11 R12 R1 H48 HRET.
pose proof HW as (Hnull & Hst & Hcc & Hc8 & Hn & HK & Hs & _).
pose proof (HK ck eq_refl) as HKo. pose proof HKo as (Hck0 & Hckl & _).
pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof Hs as (Hcl & _ & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_stack B x Hc) as HS. pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hk_call_regs B x Hc) as (_ & _ & _ & _ & _ & _ & _ & Hgp & Htp).
pose proof (hk_pod_at_cut B pb_segs_low x PAT_KEY cl _ regsT memT mdT errno_low Hc Hnull HC ltac:(lia))
  as (HG & HRA & HHV).
destruct (hgw_key_bytes x ck HKo) as (Hnz & Hkl1 & Hkl2 & _ & _).
pose proof (hgw_key_garr8 (hx_rd x memT) x ck HG HKo) as HKG.
destruct (hgw_strncmp_prefix (hp_kstr x ck) Hnz) as (d & Hd & Hdr & Hdp).
assert (Hsp : spZ regsT = hx_spa x) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
(* the key, a C string in the pod *)
assert (Hoffk : hd_off_stack regsT (2 * ESTACK) (hx_P x) (hx_len x)).
{ apply (hk_off_stack_sub (hx_regs x) regsT T_parse_STK (2 * ESTACK) (hx_P x) (hx_len x) _ _ HOFF);
  [rewrite Hsp; unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia | rewrite Hsp; unfold hx_sp in *; lia | lia | lia]. }
assert (Htlk : hd_str_tail (aview rsegs (w_H (hx_W x)) memT) (hx_P x + ck + 8 + Z.of_nat (length (hp_kstr x ck)))).
{ apply (hgw_str_tail (w_H (hx_W x)) memT (hx_P x) (hd_zbytes (hx_bs x)) _ HG);
  unfold hd_zbytes; rewrite ?length_map; unfold hx_len in *; [Z.div_mod_to_equations; lia | exact Hl8m | lia]. }
destruct (hk_awrap_sub (hx_W x) regsT memT (hx_P x) (hx_len x) (hx_P x + ck + 8) (hp_kstr x ck) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) HAM HRA HHV Hoffk HKG Hnz Htlk) as [Hx Hmx].
(* the literal "reac.headamp." at 0x214a0 *)
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & Hkey0 & _).
assert (Eakey : hi_akey headamp_himg_B = 0x214a0) by reflexivity.
rewrite Eakey in Hkey0.
assert (Hkey : hd_cstr rsegs (w_H (hx_W x)) memT 0x214a0 (hd_zbytes Headamp.HA_PREFIX)).
{ apply (hk_cstr_at_cut B pb_segs_low x PAT_KEY cl _ regsT memT mdT _ _ errno_low Hc HC ltac:(lia)
    ltac:(reflexivity) Hkey0).
  intros i Hi. unfold hd_zbytes in Hi. rewrite length_map, hgw_prefix_len in Hi. rewrite HBerrno. lia. }
assert (Hoffy : hd_off_stack regsT (2 * ESTACK) 0x214a0 (Z.of_nat (length Headamp.HA_PREFIX) + 1)).
{ intros b Hb Hw. rewrite hgw_prefix_len in Hb. rewrite Hsp in Hw.
  pose proof (hk_window_band B x b Hc ltac:(unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia)) as Hwb.
  pose proof alloc_ceiling_value as [[AC1 AC2] _]. lia. }
destruct (hk_awrap_cstr pb_segs_low (hx_W x) regsT memT 0x214a0 Headamp.HA_PREFIX Hkey Hoffy) as [Hy Hmy].
(* the read-only image bytes the wrapper reads *)
assert (Hro : forall a, in_rom rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview rsegs (w_H (hx_W x)) memT a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a))).
{ exact (hk_aro_at_cut B pb_segs_low x PAT_KEY cl _ regsT memT mdT Hc HC ltac:(lia)). }
pose proof HS as (_ & _ & S3 & S4 & _ & _ & S7 & S8 & S9 & S10 & _).
assert (Ho16 : (hx_spa x - hx_sp0 x) mod 16 = 0) by (clear - S8 S9; Z.div_mod_to_equations; lia).
assert (Hbud : 2 * ESTACK - (hx_spa x - hx_sp0 x) <= hx_STK x)
by (clear - S3 S10; unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia).
assert (Hsp' : spZ regsT = hx_sp0 x + (hx_spa x - hx_sp0 x)) by (rewrite Hsp; lia).
assert (Hneg : hx_spa x - hx_sp0 x <= 0) by (unfold hx_sp in *; lia).
assert (Hgp' : getr regsT 3 = w64 (as_gp B)) by (rewrite C3; exact Hgp).
assert (Htp' : getr regsT 4 = w64 (as_tp B)) by (rewrite C4; exact Htp).
assert (Hraw : YK0s.ret_ok (w64 PC_WRET)) by (apply ret_ok_even; vm_compute; reflexivity).
eapply SRr_bind.
{ exact (hj_strncmp_at (fx := mkFP F fc) rsegs B pb_segs_low B_TRAMP_STRNCMP (STRNCMP F fc) (hx_W x) regsT memT
    (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x) (hx_lyc x)
    (hx_Sc x) mdT (hx_k x) (hx_P x + ck + 8) 0x214a0 13 (hp_kstr x ck) Headamp.HA_PREFIX d (hx_spa x - hx_sp0 x)
    (w64 PC_WRET) (hx_fr x) PAT_KEY (proj1 HC) R10 R11 R12 ltac:(lia) Hsp' Ho16 Hneg Hbud Hgp' Htp' R1 Hraw
    Hx Hy Hmx Hmy Hd Hro). }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hio2 & (v & Hv & Hvd) & HK2 & Hpres2).
assert (HK2' : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 2 * ESTACK <= a < hx_spa x) ->
  aview rsegs (w_H (hx_W x)) mem2 a = aview rsegs (w_H (hx_W x)) memT a).
{ intros a Ha Hw. apply HK2; [exact Ha|]. replace (hx_sp0 x + (hx_spa x - hx_sp0 x)) with (hx_spa x) by lia. exact Hw. }
pose proof alloc_ceiling_value as [[AC1 AC2] _].
assert (Herr2 : exists ev', rd32 (hx_view x mem2) (as_errno B) ev').
{ destruct (hk_core_cells B x _ _ _ _ _ _ HC) as (_ & _ & (ev' & Hev)). exists ev'.
  apply (hk_rd32_kept (hx_view x memT)); [|exact Hev].
  intros j Hj. unfold hx_view. apply HK2'; rewrite HBerrno; [lia|].
  pose proof (hk_window_band B x (hx_spa x - 2 * ESTACK) Hc ltac:(unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia)).
  lia. }
assert (HC2 : hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2).
{ apply (hk_core_of_call B pb_segs_low x PAT_KEY cl _ regsT memT mdT regs2 mem2 md2 errno_low Hc HC ltac:(lia)
    ltac:(reflexivity) HJ2 HP2 Hio2); [|exact Herr2].
  intros a Ha Hw _ _. unfold hx_view. apply HK2'; [exact Ha|]. intros Hw'. apply Hw. unfold ESTACK in *. lia. }
apply (HRET F fc regs2 mem2 md2).
apply (pbW_ret_at x r cc n ck cl keys rf F fc regsT memT regs2 mem2 md2 Hc HC2 Hfx HW Hin HL R23 R24 R25 H48 HP2 HK2').
rewrite Hv. split; intros H0; [apply Hdp, Hvd, H0 | apply Hvd, Hdp, H0].
Qed.

(* ======================================= the engine's plumbing ======================================= *)
(* the regions of every run here: read-only ones, and the temporaries at sp = spa (atom 2) writable inside
   [spa, spa + 0x80) *)
Definition pbW_rgood (r : YP09.region) : bool :=
(YP09.r_whi r <=? YP09.r_wlo r) ||
(obase_eqb (YP09.r_base r) (Some 2%nat) && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0x80)).

Lemma pbW_wr : forall E rs a spa, bv_unsigned (ew E 2) = spa -> forallb pbW_rgood rs = true ->
in_wrange E rs a -> spa <= a < spa + 0x80.
Proof.
intros E rs a spa H2 Hg (rg & Hin & Ha). pose proof (proj1 (forallb_forall _ _) Hg rg Hin) as Hr.
unfold pbW_rgood in Hr. apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
apply andb_prop in Hr as [Hr Hhi]. apply andb_prop in Hr as [Hb Hlo]. apply Z.leb_le in Hhi, Hlo.
destruct (YP09.r_base rg) as [b|] eqn:Eb; [|discriminate Hb]. cbn in Hb. apply Nat.eqb_eq in Hb. subst b.
cbn [base_val] in Ha. lia.
Qed.

Lemma pbW_awr : forall (x : pctx) E rs bl0 blc ly own U, call_ok B x -> bv_unsigned (ew E 2) = hx_spa x ->
forallb pbW_rgood rs = true -> awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) bl0 blc ly own U.
Proof.
intros x E rs bl0 blc ly own U Hc H2 Hg a Ha. pose proof (pbW_wr E rs a _ H2 Hg Ha) as Hw.
pose proof (hk_stack B x Hc) as HS. pose proof (hk_frame_win B x Hc) as HW.
left. left. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
Qed.

(* a run's frame keeps every byte outside the temporaries *)
Lemma pbW_keep : forall (x : pctx) E rs (m0 m m' : word -> option byte), bv_unsigned (ew E 2) = hx_spa x ->
forallb pbW_rgood rs = true -> frame_of E rs m m' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) -> m (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) -> m' (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
Proof.
intros x E rs m0 m m' H2 Hg HF HK a Ha Hn. rewrite (HF (Z_to_bv 64 a)); [exact (HK a Ha Hn)|].
rewrite unsigned_lit_small by exact Ha. intros Hw. exact (Hn (pbW_wr E rs a _ H2 Hg Hw)).
Qed.

(* the registers every cut keeps, as the symbolic state holds them *)
Definition pbW_fixed (sr : list sv) : Prop :=
sr_get sr 2%bv = SOff 2 0 /\ sr_get sr 3%bv = SOff 3 0 /\ sr_get sr 4%bv = SOff 4 0 /\ sr_get sr 8%bv = SOff 8 0 /\
sr_get sr 9%bv = SOff 9 0 /\ sr_get sr 18%bv = SOff 18 0 /\ sr_get sr 19%bv = SOff 19 0 /\
sr_get sr 26%bv = SOff 26 0 /\ sr_get sr 27%bv = SOff 27 0.
Ltac pbW_fixed_tac := repeat split; vm_compute; reflexivity.

(* a register the run left as an atom of the entry env *)
Lemma pbW_reg_kept : forall F fc E0 E ss ms (H : word -> bool) k n (r : bv 5),
st_ok (fx := mkFP F fc) rsegs E ss (restrict H ms) -> env_agree k E0 E -> (n < k)%nat ->
sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E0 n.
Proof.
intros F fc E0 E ss ms H k n r HS HAE Hn Hsr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, hk_sv_SOff0. exact (proj1 HAE n Hn).
Qed.

Lemma pbW_reg_U : forall F fc E ss ms (H : word -> bool) (r : bv 5) v,
st_ok (fx := mkFP F fc) rsegs E ss (restrict H ms) -> U E (sr_get (ss_regs ss) r) = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros F fc E ss ms H r v HS Hv. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), denot_lit_U, Hv. reflexivity.
Qed.

(* a frame temporary the run's state holds as a chunk of the temporaries region *)
Lemma pbW_temps_val : forall F fc (x : pctx) E ss ms cs o v w,
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> In (hk_temps cs) (ss_mem ss) ->
bv_unsigned (ew E 2) = hx_spa x -> In (YP09.mkChunk o (CVal 8 v)) cs -> U E v = w -> 
val_mem rsegs (hx_rd x (ms_mem ms)) (hx_spa x + o) 8 w.
Proof.
intros F fc x E ss ms cs o v w HS Hin H2 Hc Hv.
pose proof (st_ok_mem_ok rsegs E ss _ HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR _ Hin) as HT. cbn [ms_mem restrict] in HT.
unfold region_ok, hk_temps in HT. cbn [YP09.r_base YP09.r_chunks base_val] in HT. rewrite H2 in HT.
destruct HT as (_ & _ & _ & HC). pose proof (proj1 (Forall_forall _ _) HC _ Hc) as Hck.
pose proof (U_range E v) as R. rewrite Hv in R. unfold M64 in R.
exact (val_of_chunk_ok rsegs E _ _ o 8 v w Hck ltac:(rewrite denot_lit_U, Hv; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* hp_core at a stop of a run that wrote only the temporaries *)
Lemma pbW_stop : forall F fc (x : pctx) pat cl rb regs mem md L E ss ms md2 k,
call_ok B x -> hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 -> length rb = 12%nat ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> env_agree k (hk_env x regs L) E -> (28 <= k)%nat ->
pbW_fixed (ss_regs ss) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
hp_core B x pat cl rb (ms_regs ms) (ms_mem ms) md2.
Proof.
intros F fc x pat cl rb regs mem md L E ss ms md2 k Hc HC Hcl Hrb HS HAE Hk (F2 & F3 & F4 & F8 & F9 & F18 & F19 & F26 & F27)
  HJ Hio KM.
apply (hk_core_frame B pb_segs_low x pat cl rb regs mem md (ms_regs ms) (ms_mem ms) md2 0 0x80 errno_low Hc HC Hcl Hrb);
  [lia | lia | intros a Ha Hn; apply KM; [exact Ha | lia] | exact HJ | exact Hio |].
apply (hk_cregs_same x regs (ms_regs ms) (hk_core_cregs B x _ _ _ _ _ _ HC));
[ rewrite (pbW_reg_kept F fc _ E ss ms _ k 2 2%bv HS HAE ltac:(lia) F2); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 3 3%bv HS HAE ltac:(lia) F3); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 4 4%bv HS HAE ltac:(lia) F4); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 8 8%bv HS HAE ltac:(lia) F8); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 9 9%bv HS HAE ltac:(lia) F9); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 18 18%bv HS HAE ltac:(lia) F18); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 19 19%bv HS HAE ltac:(lia) F19); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 26 26%bv HS HAE ltac:(lia) F26); apply hk_env_reg; reflexivity
| rewrite (pbW_reg_kept F fc _ E ss ms _ k 27 27%bv HS HAE ltac:(lia) F27); apply hk_env_reg; reflexivity ].
Qed.

(* the entry state at a cut: the saves, the temporaries with the segment's chunks, the segment's regions *)
Lemma pbW_entry : forall F fc (x : pctx) pat cl rb regs mem md L pc sr cs rs fs,
call_ok B x -> hp_core B x pat cl rb regs mem md ->
regs_ok (hk_env x regs L) sr regs ->
regions_wf (hk_saves :: hk_temps cs :: rs) = true ->
Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) cs ->
Forall (region_ok rsegs (hk_env x regs L) (hx_rd x mem)) rs ->
pairwise_disjoint (hk_env x regs L) (hk_saves :: hk_temps cs :: rs) ->
atoms_ok (hk_env x regs L) fs ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs L)
  (mkSS pc sr (hk_saves :: hk_temps cs :: rs) None (mkFacts (hk_atoms ++ fs) [] []))
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros F fc x pat cl rb regs mem md L pc sr cs rs fs Hc HC Hsr Hwf Hcs Hrs Hpd Hfs.
rewrite restrict_mkst_fx. unfold hk_env in *. apply (entry_st_ok_full rsegs); [exact Hsr | exact Hwf | | exact Hpd |].
- apply Forall_cons; [exact (hk_saves_ok B x pat cl rb regs mem md L Hc HC)|].
  apply Forall_cons; [exact (hk_temps_ok B x pat cl rb regs mem md L cs Hc HC Hcs) | exact Hrs].
- split; [|split; exact I]. exact (hk_atoms_ok B x regs L fs Hc (hk_core_cregs B x _ _ _ _ _ _ HC) Hfs).
Qed.

(* the three frame temporaries the pair loop reads back: [spa + 16], rf at [spa + 32], the body at [spa + 40] *)
Definition pbW_tcs (a : nat) : list YP09.chunk :=
[YP09.mkChunk 0x10 (CVal 8 (SOff a 0)); YP09.mkChunk 0x20 (CVal 8 (SOff (S a) 0));
 YP09.mkChunk 0x28 (CVal 8 (SOff (S (S a)) 0))].

Lemma pbW_tcs_ok : forall (x : pctx) regs mem L r cl rf (a : nat), pb_loop x r cl rf regs mem ->
ew (hk_env x regs L) a = w64 ((hx_P x + r + 8) mod 8 + 3) -> ew (hk_env x regs L) (S a) = w64 rf ->
ew (hk_env x regs L) (S (S a)) = w64 (hx_P x + r + 16) ->
0 <= (hx_P x + r + 8) mod 8 + 3 < 2 ^ 64 -> 0 <= rf < 2 ^ 64 -> 0 <= hx_P x + r + 16 < 2 ^ 64 ->
Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) (pbW_tcs a).
Proof.
intros x regs mem L r cl rf a (_ & _ & _ & L16 & L32 & L40) E1 E2 E3 R1 R2 R3. unfold pbW_tcs.
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val rsegs _ _ _ 0x10 8 (SOff a 0) ((hx_P x + r + 8) mod 8 + 3));
  [rewrite hk_sv_SOff0, E1; reflexivity | cbn; lia | lia | exact L16].
- apply (chunk_ok_val rsegs _ _ _ 0x20 8 (SOff (S a) 0) rf); [rewrite hk_sv_SOff0, E2; reflexivity | cbn; lia | lia | exact L32].
- apply (chunk_ok_val rsegs _ _ _ 0x28 8 (SOff (S (S a)) 0) (hx_P x + r + 16));
  [rewrite hk_sv_SOff0, E3; reflexivity | cbn; lia | lia | exact L40].
Qed.

(* the shadow address of s7 (and of s6) in the engine's form (srli x,3; add x,x,s11) *)
Definition pbW_a7e : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 27 0).
Definition pbW_s5e : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 27 0).

Lemma pbW_bv_ne0 : forall n, 0 < n < 32 -> Z_to_bv 5 n <> 0%bv.
Proof.
intros n Hn E. assert (H0 : bv_unsigned (Z_to_bv 5 n) = bv_unsigned (0%bv : bv 5)) by (rewrite E; reflexivity).
rewrite Z_to_bv_unsigned in H0. unfold bv_wrap in H0. change (bv_modulus 5) with 32 in H0.
rewrite Z.mod_small in H0 by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in H0. lia.
Qed.

Ltac pbW_in := vm_compute; repeat first [left; reflexivity | right].

(* ======================================= ADV 0x84edc ======================================= *)
(* 0x84edc lb a0,0(a7): the check of s7 (shadow entry mkSHE 23 0 8: the child's header is in the pod), lwu CS,
   s7 += ((CS + 7) | 7) + 1 = round_up8 (8 + CS); 0x84efc beqz (s7 & 3): taken (the next child is aligned), back to
   WALK 0x84cb4. Env: L = [CS; [spa + 16]; rf; P + r + 16] at slots 47 .. 50. *)
Definition pbW_fD : list (nat * afact) := [(23%nat, mkAF 16 (2 ^ 47 - 16) 3); (47%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition pbW_ssD : sstate := mkSS PC_ADV (sr_set sr_atoms 17%bv pbW_a7e)
  (hk_saves :: hk_temps (pbW_tcs 48) :: [YP09.mkRegion (Some 23%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 47 0))]])
  None (mkFacts (hk_atoms ++ pbW_fD) [] []).
Definition pbW_SHD : list shent := [mkSHE 23 0 8].
Definition pbW_LD (x : pctx) (r cc rf : Z) : list word :=
[w64 (Spa.u32_at (hx_bs x) cc); w64 ((hx_P x + r + 8) mod 8 + 3); w64 rf; w64 (hx_P x + r + 16)].

Lemma pbW_adv_exit : forall F fc (x : pctx) r cc n ko cl keys rf regs mem md E ss ms md2 k,
call_ok B x -> ADV_at B x r cc n ko cl keys rf F fc regs mem md ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_WALK ->
env_agree k (hk_env x regs (pbW_LD x r cc rf)) E -> (51 <= k)%nat -> pbW_fixed (ss_regs ss) ->
sr_get (ss_regs ss) 14%bv = SOff 14 0 -> sr_get (ss_regs ss) 16%bv = SOff 16 0 ->
sr_get (ss_regs ss) 20%bv = SOff 20 0 -> sr_get (ss_regs ss) 21%bv = SOff 21 0 ->
sr_get (ss_regs ss) 22%bv = SOff 22 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 ->
sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + hp_next x cc ->
In (hk_temps (pbW_tcs 48)) (ss_mem ss) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
(forall cc', WALK_ok B MT x r cc' n ko cl keys rf) ->
SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ko cl keys rf regs mem md E ss ms md2 k Hc HA HS Hrv Hpc HAE Hk Hfix F14 F16 F20 F21 F22 F24 F25
  U23 Hin HJ Hio KM HWALK.
pose proof HA as (HC & Hfx & HM & HL & (R14 & R16) & R23 & R24 & R25 & R17).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hci & Hn & HK & Hs & HW).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS. unfold hp_vs in *.
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & _).
set (L := pbW_LD x r cc rf) in *.
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & _ & _ & _ & HP63 & _).
assert (U2 : bv_unsigned (ew E 2) = hx_spa x).
{ rewrite (proj1 HAE 2%nat ltac:(lia)), (hk_env_reg x regs L 2 2%bv eq_refl), C2. apply unsigned_lit_small. lia. }
assert (UL : forall j v, (j < 4)%nat -> nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E (SOff (47 + j) 0) = v).
{ intros j v Hj Hv Hr. apply U_atom; [|exact Hr]. rewrite (proj1 HAE (47 + j)%nat ltac:(lia)), hk_env_seg. exact Hv. }
rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E ss ms HS Hrv), Hpc.
apply (HWALK (hp_next x cc) F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE ltac:(lia) Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact (hgw_adv_walk x r cc n ko cl keys rf HM)|].
split.
{ unfold pb_loop.
  rewrite (pbW_reg_kept F fc _ E ss ms _ k 20 20%bv HS HAE ltac:(lia) F20), (hk_env_reg x regs L 20 20%bv eq_refl).
  rewrite (pbW_reg_kept F fc _ E ss ms _ k 21 21%bv HS HAE ltac:(lia) F21), (hk_env_reg x regs L 21 21%bv eq_refl).
  rewrite (pbW_reg_kept F fc _ E ss ms _ k 22 22%bv HS HAE ltac:(lia) F22), (hk_env_reg x regs L 22 22%bv eq_refl).
  split; [exact L20|]. split; [exact L21|]. split; [exact L22|].
  pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)).
  split; [apply (pbW_temps_val F fc x E ss ms (pbW_tcs 48) 0x10 (SOff 48 0) _ HS Hin U2 ltac:(cbn; tauto));
    apply (UL 1%nat); [lia | reflexivity | lia]|].
  split; [apply (pbW_temps_val F fc x E ss ms (pbW_tcs 48) 0x20 (SOff 49 0) _ HS Hin U2 ltac:(cbn; tauto));
    apply (UL 2%nat); [lia | reflexivity | lia]|].
  apply (pbW_temps_val F fc x E ss ms (pbW_tcs 48) 0x28 (SOff 50 0) _ HS Hin U2 ltac:(cbn; tauto)).
  apply (UL 3%nat); [lia | reflexivity | lia]. }
split.
{ split.
  - rewrite (pbW_reg_kept F fc _ E ss ms _ k 14 14%bv HS HAE ltac:(lia) F14), (hk_env_reg x regs L 14 14%bv eq_refl). exact R14.
  - rewrite (pbW_reg_kept F fc _ E ss ms _ k 16 16%bv HS HAE ltac:(lia) F16), (hk_env_reg x regs L 16 16%bv eq_refl). exact R16. }
split; [exact (pbW_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split.
- rewrite (pbW_reg_kept F fc _ E ss ms _ k 24 24%bv HS HAE ltac:(lia) F24), (hk_env_reg x regs L 24 24%bv eq_refl). exact R24.
- rewrite (pbW_reg_kept F fc _ E ss ms _ k 25 25%bv HS HAE ltac:(lia) F25), (hk_env_reg x regs L 25 25%bv eq_refl). exact R25.
Qed.

(* ---------------------------------- the run tactics ---------------------------------- *)
(* HAE : env_agree k E0 E (E0 the entry env, E the current one), KM : the bytes outside the temporaries as at the
   entry, Hio : same_io md0 md, U2 : bv_unsigned (ew E0 2) = hx_spa x *)
Ltac pbW_ne0 := let H0 := fresh "H0" in intros H0; apply (f_equal bv_unsigned) in H0; vm_compute in H0; discriminate H0.
Ltac pbW_post x HAE KM Hio U2 :=
  lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  lazymatch goal with HFr : frame_of E1 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KM' := fresh "KM" in
    pose proof (pbW_keep x E1 rs _ _ _ ltac:(first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2])
      ltac:(vm_compute; reflexivity) HFr KM) as KM';
    clear KM; rename KM' into KM end;
  let H' := fresh "HAE'" in assert (H' : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H' into HAE
  end end;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md _ |- _ =>
  lazymatch type of Hio with same_io ?m0 _ =>
  let H' := fresh "Hio'" in
  assert (H' : same_io m0 md)
    by (first [exact Hio | eapply same_io_trans; [exact Hio | apply same_io_materialized; apply same_but_materialized_wvb_any]]);
  clear Hio; rename H' into Hio end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac pbW_awr_tac x Hc HAE U2 :=
  apply (pbW_awr x); [exact Hc | first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2] | vm_compute; reflexivity].
Ltac pbW_run x Hc HAE KM Hio U2 :=
  lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tokH pb_tbl_ok HS HJ SHOK hk_Bspan; [pbW_awr_tac x Hc HAE U2 | ] end;
  pbW_post x HAE KM Hio U2.
Ltac pbW_run_to x Hc HAE KM Hio U2 stop :=
  lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tokH pb_tbl_ok HS HJ SHOK hk_Bspan stop; [pbW_awr_tac x Hc HAE U2 | ] end;
  pbW_post x HAE KM Hio U2.
Ltac pbW_branch HAE HB :=
  lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pb_tbl_ok HS SH hk_Bspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HB end;
  rewrite ?branch_ltu_U, ?branch_geu_U, ?branch_eq_U, ?branch_ne_U in HB;
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  first [ constr_eq E0 E1 | repeat (rewrite (U_agree k E0 E1 _ HAE) in HB by (vm_compute; reflexivity)) ] end.
Ltac pbW_ureg HAE :=
  lazymatch goal with |- U ?E (sr_get (ss_regs ?ss) ?r) = _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity) end;
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  first [constr_eq E0 E1 | rewrite (U_agree k E0 E1 _ HAE) by (vm_compute; reflexivity)] end.

Theorem segADV_ok : segADV_stmt B MT.
Proof.
unfold segADV_stmt. intros x r cc n ko cl keys rf Hc HWALK _ F fc regs mem md HA.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsl.
pose proof HA as (HC & Hfx & HM & HL & (R14 & R16) & R23 & R24 & R25 & R17).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hci & Hn & HK & Hs & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_pod_at_cut B pb_segs_low x PAT_KEY cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
pose proof (hk_pod_side B x Hc Hnull) as Hside.
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_inside_bounds _ _ _ _ Hci) as (B1 & B2 & B3).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof alloc_ceiling_value as [[AC1 AC2] _].
set (L := pbW_LD x r cc rf).
set (E0 := hk_env x regs L).
assert (E2 : ew E0 2 = w64 (hx_spa x)) by (subst E0; rewrite (hk_env_reg x regs L 2 2%bv eq_refl); exact C2).
assert (E8 : ew E0 8 = w64 (hx_sp x)) by (subst E0; rewrite (hk_env_reg x regs L 8 8%bv eq_refl); exact C8).
assert (E23 : ew E0 23 = w64 (hx_P x + cc)) by (subst E0; rewrite (hk_env_reg x regs L 23 23%bv eq_refl); exact R23).
assert (E27 : ew E0 27 = w64 SHADOW_OFF) by (subst E0; rewrite (hk_env_reg x regs L 27 27%bv eq_refl); exact C27).
assert (E47 : ew E0 47 = w64 (Spa.u32_at (hx_bs x) cc)) by exact (hk_env_seg x regs L 0).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U23 : U E0 (SOff 23 0) = hx_P x + cc) by (apply U_atom; [exact E23 | lia]).
assert (U27 : U E0 (SOff 27 0) = SHADOW_OFF) by (apply U_atom; [exact E27 | unfold SHADOW_OFF; lia]).
assert (U47 : U E0 (SOff 47 0) = Spa.u32_at (hx_bs x) cc) by (apply U_atom; [exact E47 | lia]).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pbW_ssD
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_ADV) mem (seg_rom rsegs)))).
{ unfold pbW_ssD. apply (pbW_entry F fc x PAT_KEY cl _ regs mem md L PC_ADV _ _ _ _ Hc HC).
  - apply regs_ok_pin; [unfold hk_env; apply regs_ok_Ereg | pbW_ne0 |].
    rewrite denot_lit_U. fold E0. unfold pbW_a7e. rewrite (hgw_U_shadow E0 23 _ U23 U27) by lia. exact R17.
  - vm_compute. reflexivity.
  - apply (pbW_tcs_ok x regs mem L r cl rf 48 HL);
    [exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2) | exact (hk_env_seg x regs L 3)
    | pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)); lia | lia | lia].
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E0.
    rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 47 0) (Spa.u32_at (hx_bs x) cc));
    [rewrite hk_sv_SOff0; exact E47 | cbn; lia | lia |].
    rewrite Z.add_0_r. apply hgw_pod_u32; [exact HG | lia | unfold hx_len in *; lia].
  - apply pairwise_disjoint_of_extents. unfold hk_saves, hk_temps.
    cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
    rewrite E2, E8, E23, !unsigned_lit_small by (unfold hx_sp in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. destruct Hside; repeat split; lia.
  - cbn [atoms_ok pbW_fD]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
    rewrite E23, E47, !unsigned_lit_small by lia. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    rewrite Z.mod_1_r. repeat split; try lia; clear - HP16 Hc8; Z.div_mod_to_equations; lia. }
assert (SHOK : sh_ok rsegs hk_Bx pbW_SHD E0 (hx_rd x mem)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (hk_shent_pod B x (w_H (hx_W x)) mem E0 23 cc 0 8 Hc Hnull E27 E23 HRA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 51 E0 E0) by apply env_agree_refl.
destruct (hgw_lor7 (Spa.u32_at (hx_bs x) cc) ltac:(lia)) as (LR1 & LR2 & LR3).
assert (Un : U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SOff 23 0) (SAlu ALU_OR (SOff 47 7) (SLit 7))) (SLit 1)) =
  hx_P x + cc + Spa.round_up8 (8 + Spa.u32_at (hx_bs x) cc)) by (apply hgw_U_next; lia).
assert (Un4 : (hx_P x + cc + Spa.round_up8 (8 + Spa.u32_at (hx_bs x) cc)) mod 4 = 0).
{ rewrite <- LR2. clear - HP16 Hc8 LR3. Z.div_mod_to_equations. lia. }
unfold cfg_at. change (w64 PC_ADV) with (Z_to_bv 64 PC_ADV).
(* 0x84edc .. 0x84ef8: the check of s7, s7 += round_up8 (8 + CS); stop at 0x84efc beqz (s7 & 3) *)
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB.
- (* taken: 0x84cb4 *)
  pbW_run_to x Hc HAE KM Hio U2 PC_WALK.
  eapply (pbW_adv_exit F fc x r cc n ko cl keys rf regs mem md _ _ _ _ 51 Hc HA HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | pbW_ureg HAE; rewrite Un; unfold hp_next; lia | pbW_in | exact HJ | exact Hio | exact KM | exact HWALK ].
- (* not taken: impossible, the next child is aligned *)
  exfalso. rewrite (hgw_U_and3 E0 _ _ Un Un4), U_lit in HB by lia. discriminate HB.
Qed.

(* ======================================= the exits of WALK and of its inner cuts ======================================= *)
Lemma pbW_cfg_stop : forall F fc E ss ms (H : word -> bool) pc md2,
st_ok (fx := mkFP F fc) rsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = pc ->
mkCfg ms md2 = cfg_at (fx := mkFP F fc) rsegs pc (ms_regs ms) (ms_mem ms) md2.
Proof. intros F fc E ss ms H pc md2 HS Hrv Hpc. rewrite (st_ok_restrict_mkst rsegs H E ss ms HS Hrv), Hpc. reflexivity. Qed.

(* the pair loop's registers and frame temporaries at a stop *)
Lemma pbW_loop_stop : forall F fc (x : pctx) r cl rf E ss ms cs v1 v2 v3,
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = hx_P x + r + 16 ->
pb_loop x r cl rf (ms_regs ms) (ms_mem ms).
Proof.
intros F fc x r cl rf E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3.
split; [exact (pbW_reg_U F fc E ss ms _ 20%bv _ HS U20)|].
split; [exact (pbW_reg_U F fc E ss ms _ 21%bv _ HS U21)|].
split; [exact (pbW_reg_U F fc E ss ms _ 22%bv _ HS U22)|].
split; [exact (pbW_temps_val F fc x E ss ms cs 0x10 v1 _ HS Hin U2 C1 V1)|].
split; [exact (pbW_temps_val F fc x E ss ms cs 0x20 v2 _ HS Hin U2 C2 V2)|].
exact (pbW_temps_val F fc x E ss ms cs 0x28 v3 _ HS Hin U2 C3 V3).
Qed.

(* s9 = keys (no bound on keys: the register as an atom of the entry env) *)
Lemma pbW_keys : forall F fc (x : pctx) regs L E ss ms k keys,
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> env_agree k (hk_env x regs L) E -> (28 <= k)%nat ->
sr_get (ss_regs ss) 25%bv = SOff 25 0 -> getr regs 25%bv = w64 keys -> getr (ms_regs ms) 25%bv = w64 keys.
Proof.
intros F fc x regs L E ss ms k keys HS HAE Hk F25 R25.
rewrite (pbW_reg_kept F fc _ E ss ms _ k 25 25%bv HS HAE ltac:(lia) F25), (hk_env_reg x regs L 25 25%bv eq_refl). exact R25.
Qed.
Ltac pbW_k25 HAE R25 :=
  lazymatch goal with |- getr (ms_regs ?ms) _ = _ =>
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ms) |- _ =>
  exact (pbW_keys _ _ _ _ _ _ _ ms _ _ HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) R25) end end.

(* EXIT 0x85218: the child at cc is not inside the Struct body *)
Lemma pbW_exit_exit : forall F fc (x : pctx) r cc n ko cl keys rf regs mem md L E ss ms md2 k cs v2,
call_ok B x -> WALK_at B x r cc (S n) ko cl keys rf F fc regs mem md ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_EXIT ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> pbW_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) -> getr (ms_regs ms) 25%bv = w64 keys ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
EXIT_ok B MT x -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ko cl keys rf regs mem md L E ss ms md2 k cs v2 Hc HWk HS Hrv Hpc HAE Hk Hfix U20 U25 Hin U2 C2 V2
  Hout HJ Hio KM HEXIT.
pose proof HWk as (HC & (Hfx & _) & HM & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (pbW_cfg_stop F fc E ss ms _ PC_EXIT md2 HS Hrv Hpc).
apply (HEXIT cl keys rf F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact (hgw_walk_exit x r cc n ko cl keys rf HM Hout)|].
split; [exact (pbW_reg_U F fc E ss ms _ 20%bv _ HS U20)|].
split; [exact U25|].
exact (pbW_temps_val F fc x E ss ms cs 0x20 v2 _ HS Hin U2 C2 V2).
Qed.

(* ADV 0x84edc with the key slot ko' *)
Lemma pbW_exit_adv : forall F fc (x : pctx) r cc n ko' cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_adv x r cc n ko' cl keys rf ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_ADV ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> pbW_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 14%bv) = hx_P x + r + 16 -> U E (sr_get (ss_regs ss) 16%bv) = 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 24%bv) = hp_keyv x ko' ->
getr (ms_regs ms) 25%bv = w64 keys -> U E (sr_get (ss_regs ss) 17%bv) = shadow_addr (hx_P x + cc) ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = hx_P x + r + 16 ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
ADV_ok B MT x r cc n ko' cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ko' cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 Hc HC Hfx HM HS Hrv Hpc HAE Hk Hfix
  U20 U21 U22 U14 U16 U23 U24 U25 U17 Hin U2 C1 V1 C2 V2 C3 V3 HJ Hio KM HADV.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (pbW_cfg_stop F fc E ss ms _ PC_ADV md2 HS Hrv Hpc).
apply (HADV F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|].
split; [exact (pbW_loop_stop F fc x r cl rf E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [split; [exact (pbW_reg_U F fc E ss ms _ 14%bv _ HS U14) | exact (pbW_reg_U F fc E ss ms _ 16%bv _ HS U16)]|].
split; [exact (pbW_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact (pbW_reg_U F fc E ss ms _ 24%bv _ HS U24)|].
split; [exact U25|].
exact (pbW_reg_U F fc E ss ms _ 17%bv _ HS U17).
Qed.

(* WLB 0x84d54 *)
Lemma pbW_exit_wlb : forall F fc (x : pctx) r cc n cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_walk x r cc (S n) None cl keys rf -> hp_child_in x r cc ->
1 <= Spa.u32_at (hx_bs x) cc < 2 ^ 20 -> Spa.u32_at (hx_bs x) (cc + 4) = 8 ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_WLB ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> pbW_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 14%bv) = hx_P x + r + 16 -> U E (sr_get (ss_regs ss) 16%bv) = 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 24%bv) = 0 ->
getr (ms_regs ms) 25%bv = w64 keys -> U E (sr_get (ss_regs ss) 17%bv) = shadow_addr (hx_P x + cc) ->
U E (sr_get (ss_regs ss) 10%bv) = hx_P x + cc + 8 + Spa.u32_at (hx_bs x) cc - 1 ->
U E (sr_get (ss_regs ss) 11%bv) = hx_P x + cc + 8 ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = hx_P x + r + 16 ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
WLB_ok x r cc n cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 Hc HC Hfx HM Hin1 Hcs Hty HS Hrv Hpc HAE Hk
  Hfix U20 U21 U22 U14 U16 U23 U24 U25 U17 U10 U11 Hin U2 C1 V1 C2 V2 C3 V3 HJ Hio KM HLB.
pose proof HM as (_ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (pbW_cfg_stop F fc E ss ms _ PC_WLB md2 HS Hrv Hpc).
apply (HLB F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|]. split; [exact Hin1|]. split; [exact Hcs|]. split; [exact Hty|].
split; [exact (pbW_loop_stop F fc x r cl rf E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [split; [exact (pbW_reg_U F fc E ss ms _ 14%bv _ HS U14) | exact (pbW_reg_U F fc E ss ms _ 16%bv _ HS U16)]|].
split; [exact (pbW_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact (pbW_reg_U F fc E ss ms _ 24%bv _ HS U24)|].
split; [exact U25|].
split; [exact (pbW_reg_U F fc E ss ms _ 17%bv _ HS U17)|].
split; [exact (pbW_reg_U F fc E ss ms _ 10%bv _ HS U10) | exact (pbW_reg_U F fc E ss ms _ 11%bv _ HS U11)].
Qed.

(* KEY 0x84db0: strncmp returned 0 *)
Lemma pbW_exit_key : forall F fc (x : pctx) r cc n ck cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 v4,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_key x r cc n ck cl keys rf ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_KEY ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> pbW_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 24%bv) = hx_P x + ck + 8 ->
getr (ms_regs ms) 25%bv = w64 keys ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = rf ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x30 (CVal 8 v4)) cs -> U E v4 = shadow_addr (hx_P x + cc) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
KEY_ok B MT x r cc n ck cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ck cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 v4 Hc HC Hfx HM HS Hrv Hpc HAE Hk Hfix
  U20 U21 U22 U23 U24 U25 Hin U2 C1 V1 C2 V2 C3 V3 C4 V4 HJ Hio KM HKEY.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (pbW_cfg_stop F fc E ss ms _ PC_KEY md2 HS Hrv Hpc).
apply (HKEY F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (pbW_stop F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k Hc HC ltac:(lia) eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|].
split; [exact (pbW_loop_stop F fc x r cl rf E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [exact (pbW_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact (pbW_reg_U F fc E ss ms _ 24%bv _ HS U24)|].
split; [exact U25|].
exact (pbW_temps_val F fc x E ss ms cs 0x30 v4 _ HS Hin U2 C4 V4).
Qed.

Ltac pbW_uat HAE H := first [exact H | rewrite (U_agree _ _ _ _ HAE) by (vm_compute; reflexivity); exact H].
Ltac pbW_ukept HAE H := pbW_ureg HAE; exact H.

(* ======================================= WLB 0x84d54 ======================================= *)
(* 0x84d54 .. 0x84d60: the 1-byte check of a0 = s7 + 8 + CS - 1 (shadow entry mkSHE 10 0 1), lbu b; s8 = (b = 0 ?
   a1 : 0); j ADV. Env: L = [b; [spa + 16]; rf; P + r + 16] at slots 47 .. 50. *)
Definition pbW_fL : list (nat * afact) :=
[(10%nat, mkAF 24 (2 ^ 47 - 9) 0); (11%nat, mkAF 24 (2 ^ 47 - 16) 3); (47%nat, mkAF 0 255 0)].
Definition pbW_ssL : sstate := mkSS PC_WLB sr_atoms
  (hk_saves :: hk_temps (pbW_tcs 48) :: [YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 47 0))]])
  None (mkFacts (hk_atoms ++ pbW_fL) [] []).
Definition pbW_SHL : list shent := [mkSHE 10 0 1].

Lemma pbW_lb_ok : forall (x : pctx) r cc n cl keys rf, call_ok B x ->
(forall ko', ADV_ok B MT x r cc n ko' cl keys rf) -> WLB_ok x r cc n cl keys rf.
Proof.
intros x r cc n cl keys rf Hc HADV F fc regs mem md HLB.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsl.
pose proof HLB as (HC & Hfx & HM & Hci & Hcs & Hty & HL & (R14 & R16) & R23 & R24 & R25 & R17 & R10 & R11).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_pod_at_cut B pb_segs_low x PAT_KEY cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
pose proof (hk_pod_side B x Hc Hnull) as Hside.
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_inside_bounds _ _ _ _ Hci) as (B1 & B2 & B3).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof alloc_ceiling_value as [[AC1 AC2] _]. pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
set (o := cc + 8 + Spa.u32_at (hx_bs x) cc - 1) in *.
set (b := bv_unsigned (nth (Z.to_nat o) (hx_bs x) Cursor.NUL)).
destruct (hgw_pod_u8 (hx_rd x mem) (hx_P x) (hx_bs x) o HG ltac:(lia) ltac:(unfold hx_len in *; lia)) as [Vb Rb].
fold b in Vb, Rb.
set (L := [w64 b; w64 ((hx_P x + r + 8) mod 8 + 3); w64 rf; w64 (hx_P x + r + 16)]).
set (E0 := hk_env x regs L).
assert (EG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> ew E0 n = w64 v).
{ intros n0 rg v Hn0 Hv. subst E0. rewrite (hk_env_reg x regs L n0 rg Hn0). exact Hv. }
assert (UG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff n 0) = v) by (intros n0 rg v Hn0 Hv Hr; apply U_atom; [exact (EG n0 rg v Hn0 Hv) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v Hv Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl C2); apply unsigned_lit_small; lia).
assert (E10 : ew E0 10 = w64 (hx_P x + o)) by (rewrite (EG 10%nat 10%bv _ eq_refl R10); unfold o; f_equal; lia).
assert (E27 : ew E0 27 = w64 SHADOW_OFF) by exact (EG 27%nat 27%bv _ eq_refl C27).
assert (U47 : U E0 (SOff 47 0) = b) by (apply (UL 0%nat); [reflexivity | lia]).
assert (U11 : U E0 (SOff 11 0) = hx_P x + cc + 8) by (apply (UG 11%nat 11%bv); [reflexivity | exact R11 | lia]).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pbW_ssL
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_WLB) mem (seg_rom rsegs)))).
{ unfold pbW_ssL. apply (pbW_entry F fc x PAT_KEY cl _ regs mem md L PC_WLB _ _ _ _ Hc HC).
  - unfold hk_env. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply (pbW_tcs_ok x regs mem L r cl rf 48 HL);
    [exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2) | exact (hk_env_seg x regs L 3) | lia | lia | lia].
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E0.
    rewrite E10, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 47 0) b); [rewrite hk_sv_SOff0; exact (hk_env_seg x regs L 0) | cbn; lia | lia |].
    rewrite Z.add_0_r. exact Vb.
  - apply pairwise_disjoint_of_extents. unfold hk_saves, hk_temps.
    cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
    rewrite (EG 2%nat 2%bv _ eq_refl C2), (EG 8%nat 8%bv _ eq_refl C8), E10, !unsigned_lit_small by (unfold hx_sp in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. destruct Hside; repeat split; lia.
  - cbn [atoms_ok pbW_fL]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
    assert (E47 : ew E0 47 = w64 b) by exact (hk_env_seg x regs L 0).
    rewrite E10, (EG 11%nat 11%bv _ eq_refl R11), E47, !unsigned_lit_small by lia.
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold o. repeat split; try lia. all: clear - HP16 Hc8; Z.div_mod_to_equations; lia. }
assert (SHOK : sh_ok rsegs hk_Bx pbW_SHL E0 (hx_rd x mem)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (hk_shent_pod B x (w_H (hx_W x)) mem E0 10 o 0 1 Hc Hnull E27 E10 HRA ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold hx_len in *; lia)). }
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 51 E0 E0) by apply env_agree_refl.
unfold cfg_at. change (w64 PC_WLB) with (Z_to_bv 64 PC_WLB).
(* 0x84d54 .. 0x84d74: the check of the last body byte, lbu, the mask; j 0x84edc *)
pbW_run_to x Hc HAE KM Hio U2 PC_ADV.
eapply (pbW_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 51 (pbW_tcs 48) (SOff 48 0) (SOff 49 0)
  (SOff 50 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hci) HS);
[ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
| pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
| pbW_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(unfold shadow_addr, SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | pose proof (Z.div_le_upper_bound (hx_P x + r + 8) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia]))
| pbW_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
| pbW_ukept HAE (UG 14%nat 14%bv _ eq_refl R14 ltac:(lia))
| pbW_ukept HAE (UG 16%nat 16%bv _ eq_refl R16 ltac:(lia))
| pbW_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
| pbW_ureg HAE; rewrite (pbW_U_mask E0 47 11 b (hx_P x + cc + 8) U47 U11 Rb), (pbW_keyv_lb x cc ltac:(lia) Hcs Hty);
  fold o b; reflexivity
| pbW_k25 HAE R25
| pbW_ukept HAE (UG 17%nat 17%bv _ eq_refl R17 ltac:(unfold shadow_addr, SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | pose proof (Z.div_le_upper_bound (hx_P x + cc) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia]))
| pbW_in | exact U2
| pbW_in | pbW_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
| pbW_in | pbW_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
| pbW_in | pbW_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
| exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ].
Qed.

(* ======================================= WRET 0x84d98 ======================================= *)
(* 0x84d98 beqz a0: taken (strncmp = 0, the key has the prefix) -> KEY 0x84db0; else s8 = 0, a4 = [spa + 40],
   a6 = 8, a7 = [spa + 48]; j ADV (the pair is skipped). Env: L = [[spa + 16]; rf; P + r + 16; shadow (P + cc)] at
   slots 47 .. 50. *)
Definition pbW_csR : list YP09.chunk := pbW_tcs 47 ++ [YP09.mkChunk 0x30 (CVal 8 (SOff 50 0))].
Definition pbW_ssR : sstate := mkSS PC_WRET sr_atoms [hk_saves; hk_temps pbW_csR] None (mkFacts (hk_atoms ++ []) [] []).

Lemma pbW_U_reg0 : forall (x : pctx) regs L (n : nat) (rg : bv 5), Z.of_nat n = bv_unsigned rg ->
(U (hk_env x regs L) (SOff n 0) = 0 <-> getr regs rg = w64 0).
Proof.
intros x regs L n rg Hn. rewrite U_SOff, (hk_env_reg x regs L n rg Hn). unfold zcanon, M64.
pose proof (bv_unsigned_in_range _ (getr regs rg)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
rewrite Z.add_0_r, Z.mod_small by lia. split; intros H.
- apply bv_eq. rewrite H. reflexivity.
- rewrite H. reflexivity.
Qed.

Lemma pbW_ret_ok : forall (x : pctx) r cc n ck cl keys rf, call_ok B x ->
(forall ko', ADV_ok B MT x r cc n ko' cl keys rf) -> KEY_ok B MT x r cc n ck cl keys rf -> WRET_ok x r cc n ck cl keys rf.
Proof.
intros x r cc n ck cl keys rf Hc HADV HKEY F fc regs mem md HR.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsl.
pose proof HR as (HC & Hfx & HM & Hci & HL & R23 & R24 & R25 & H48 & H10).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (HK ck eq_refl) as HKo. pose proof HKo as (Hck0 & Hckl & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_inside_bounds _ _ _ _ Hci) as (B1 & B2 & B3).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
pose proof (hgw_u32_range (hx_bs x) ck) as RCK.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof alloc_ceiling_value as [[AC1 AC2] _]. pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
assert (Hsh : forall a, 0 <= a <= 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
set (L := [w64 ((hx_P x + r + 8) mod 8 + 3); w64 rf; w64 (hx_P x + r + 16); w64 (shadow_addr (hx_P x + cc))]).
set (E0 := hk_env x regs L).
assert (EG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> ew E0 n = w64 v).
{ intros n0 rg v Hn0 Hv. subst E0. rewrite (hk_env_reg x regs L n0 rg Hn0). exact Hv. }
assert (UG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff n 0) = v) by (intros n0 rg v Hn0 Hv Hr; apply U_atom; [exact (EG n0 rg v Hn0 Hv) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v Hv Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl C2); apply unsigned_lit_small; lia).
pose proof (Hsh (hx_P x + cc) ltac:(lia)) as Rsh.
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pbW_ssR
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_WRET) mem (seg_rom rsegs)))).
{ unfold pbW_ssR. apply (pbW_entry F fc x PAT_KEY cl _ regs mem md L PC_WRET _ _ _ _ Hc HC).
  - unfold hk_env. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold pbW_csR. apply Forall_app. split.
    + apply (pbW_tcs_ok x regs mem L r cl rf 47 HL);
      [exact (hk_env_seg x regs L 0) | exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2) | lia | lia | lia].
    + apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ _ 0x30 8 (SOff 50 0) (shadow_addr (hx_P x + cc)));
      [rewrite hk_sv_SOff0; exact (hk_env_seg x regs L 3) | cbn; lia | lia | exact H48].
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. unfold hk_saves, hk_temps.
    cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
    rewrite (EG 2%nat 2%bv _ eq_refl C2), (EG 8%nat 8%bv _ eq_refl C8), !unsigned_lit_small by (unfold hx_sp in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. repeat split; lia.
  - first [exact I | apply Forall_nil | constructor]. }
assert (SHOK : sh_ok rsegs hk_Bx [] E0 (hx_rd x mem)) by apply Forall_nil.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 51 E0 E0) by apply env_agree_refl.
assert (U10 : U E0 (SOff 10 0) = 0 <-> Headamp.ha_prefix (hp_kstr x ck) = true)
by exact (iff_trans (pbW_U_reg0 x regs L 10 10%bv eq_refl) H10).
unfold cfg_at. change (w64 PC_WRET) with (Z_to_bv 64 PC_WRET).
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB.
- (* taken: strncmp = 0, KEY 0x84db0 *)
  rewrite ?U_lit in HB by lia. apply Z.eqb_eq in HB. pose proof (proj1 U10 HB) as HP.
  pbW_run_to x Hc HAE KM Hio U2 PC_KEY.
  eapply (pbW_exit_key F fc x r cc n ck cl keys rf regs mem md L _ _ _ _ 51 pbW_csR (SOff 47 0) (SOff 48 0) (SOff 49 0)
    (SOff 50 0) Hc HC Hfx (hgw_walk_key x r cc n ck cl keys rf HM Hci HP) HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
  | pbW_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
  | pbW_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
  | pbW_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
  | pbW_ukept HAE (UG 24%nat 24%bv _ eq_refl R24 ltac:(lia))
  | pbW_k25 HAE R25
  | pbW_in | exact U2
  | pbW_in | pbW_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
  | pbW_in | pbW_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
  | pbW_in | pbW_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
  | pbW_in | pbW_uat HAE (UL 3%nat _ eq_refl Rsh)
  | exact HJ | exact Hio | exact KM | exact HKEY ].
- (* not taken: strncmp <> 0, the pair is skipped; ADV with the key slot empty *)
  rewrite ?U_lit in HB by lia. apply Z.eqb_neq in HB.
  assert (HP : Headamp.ha_prefix (hp_kstr x ck) = false)
  by (destruct (Headamp.ha_prefix (hp_kstr x ck)) eqn:EP; [exfalso; exact (HB (proj2 U10 eq_refl)) | reflexivity]).
  pbW_run_to x Hc HAE KM Hio U2 PC_ADV.
  eapply (pbW_exit_adv F fc x r cc n None cl keys rf regs mem md L _ _ _ _ 51 pbW_csR (SOff 47 0) (SOff 48 0) (SOff 49 0)
    Hc HC Hfx (hgw_walk_skip x r cc n ck cl keys rf HM Hci HP) HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
  | pbW_ukept HAE (UG 21%nat 21%bv _ eq_refl L21 ltac:(apply Hsh; lia))
  | pbW_ukept HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))
  | pbW_ukept HAE (UL 2%nat _ eq_refl ltac:(lia))
  | pbW_ureg HAE; rewrite U_lit by lia; reflexivity
  | pbW_ukept HAE (UG 23%nat 23%bv _ eq_refl R23 ltac:(lia))
  | pbW_ureg HAE; rewrite U_lit by lia; reflexivity
  | pbW_k25 HAE R25
  | pbW_ukept HAE (UL 3%nat _ eq_refl Rsh)
  | pbW_in | exact U2
  | pbW_in | pbW_uat HAE (UL 0%nat _ eq_refl ltac:(lia))
  | pbW_in | pbW_uat HAE (UL 1%nat _ eq_refl ltac:(lia))
  | pbW_in | pbW_uat HAE (UL 2%nat _ eq_refl ltac:(lia))
  | exact HJ | exact Hio | exact KM | exact (HADV None) ].
Qed.

(* ======================================= WALK 0x84cb4 ======================================= *)
(* a frame temporary after a run that stored into the temporaries: the chunk at o of the run's i-th region *)
Fixpoint pbW_find (o : Z) (cs : list YP09.chunk) : option sv :=
match cs with
| [] => None
| YP09.mkChunk o' (CVal w v) :: cs' => if (o' =? o) && (w =? 8)%N then Some v else pbW_find o cs'
| _ :: cs' => pbW_find o cs'
end.

Lemma pbW_find_In : forall o cs v, pbW_find o cs = Some v -> In (YP09.mkChunk o (CVal 8 v)) cs.
Proof.
intros o cs. induction cs as [|[o' cv] cs IH]; intros v H; [discriminate H|].
destruct cv as [w v'|l|l|d s l]; cbn [pbW_find] in H; try (right; apply IH; exact H).
destruct ((o' =? o) && (w =? 8)%N) eqn:E; [|right; apply IH; exact H].
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply N.eqb_eq in E2. subst o' w.
injection H as <-. left. reflexivity.
Qed.

Lemma pbW_mem_val : forall F fc (x : pctx) E ss ms (i : nat) o v w,
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> (i < length (ss_mem ss))%nat ->
YP09.r_base (nth i (ss_mem ss) hk_saves) = Some 2%nat -> bv_unsigned (ew E 2) = hx_spa x ->
pbW_find o (YP09.r_chunks (nth i (ss_mem ss) hk_saves)) = Some v -> U E v = w ->
val_mem rsegs (hx_rd x (ms_mem ms)) (hx_spa x + o) 8 w.
Proof.
intros F fc x E ss ms i o v w HS Hi Hb H2 Hf Hv.
pose proof (st_ok_mem_ok rsegs E ss _ HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR _ (nth_In _ hk_saves Hi)) as HT. cbn [ms_mem restrict] in HT.
unfold region_ok in HT. rewrite Hb in HT. cbn [base_val] in HT. rewrite H2 in HT.
destruct HT as (_ & _ & _ & HC). pose proof (proj1 (Forall_forall _ _) HC _ (pbW_find_In _ _ _ Hf)) as Hck.
pose proof (U_range E v) as R. rewrite Hv in R. unfold M64 in R.
exact (val_of_chunk_ok rsegs E _ _ o 8 v w Hck ltac:(rewrite denot_lit_U, Hv; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Ltac pbW_tval i o HAE U2 :=
  lazymatch goal with |- val_mem _ (hx_rd _ (ms_mem ?ms)) _ 8 _ =>
  lazymatch goal with HS' : st_ok _ ?E ?ss (restrict _ ms) |- _ =>
  let v := eval vm_compute in (pbW_find o (YP09.r_chunks (nth i (ss_mem ss) hk_saves))) in
  lazymatch v with Some ?e =>
  refine (pbW_mem_val _ _ _ E ss ms i o e _ HS' _ _ _ _ _); [apply Nat.ltb_lt; vm_compute; reflexivity
    | vm_compute; reflexivity | first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2]
    | vm_compute; reflexivity | ] end end end.
Ltac pbW_greg HAE H :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
  lazymatch goal with HS' : st_ok _ ?E ?ss (restrict _ ms) |- _ =>
  apply (pbW_reg_U _ _ E ss ms _ r _ HS'); pbW_ukept HAE H end end.
Ltac pbW_glit HAE :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
  lazymatch goal with HS' : st_ok _ ?E ?ss (restrict _ ms) |- _ =>
  apply (pbW_reg_U _ _ E ss ms _ r _ HS'); pbW_ureg HAE; rewrite U_lit by lia; reflexivity end end.

(* 0x84cb4 .. 0x84cf4: the check of s6 (shadow entry mkSHE 22 0 8), VS = lwu s6, the tests of spa_pod_is_inside;
   the check of s7 (mkSHE 23 0 8) and CS = lwu s7 when the child's header lies in the Struct body (case A).
   Env: L = [VS; CS; TY; [spa + 16]; rf; P + r + 16] at slots 47 .. 52. *)
Definition pbW_s6r : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 47 0))].
Definition pbW_s7r : YP09.region :=
  YP09.mkRegion (Some 23%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 48 0)); YP09.mkChunk 4 (CVal 4 (SOff 49 0))].
Definition pbW_fW (hi23 : Z) : list (nat * afact) :=
[(14%nat, mkAF 16 (2 ^ 47 - 8) 3); (16%nat, mkAF 8 8 0); (22%nat, mkAF 8 (2 ^ 47 - 16) 3);
 (23%nat, mkAF 16 hi23 3); (47%nat, mkAF 0 (2 ^ 32 - 1) 0); (48%nat, mkAF 0 (2 ^ 32 - 1) 0);
 (49%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition pbW_ssW (fs : list (nat * afact)) (rs : list YP09.region) : sstate :=
  mkSS PC_WALK (sr_set sr_atoms 21%bv pbW_s5e) (hk_saves :: hk_temps (pbW_tcs 50) :: rs) None
    (mkFacts (hk_atoms ++ fs) [] []).
Definition pbW_LW (x : pctx) (r cc rf : Z) : list word :=
[w64 (Spa.u32_at (hx_bs x) (r + 8)); w64 (Spa.u32_at (hx_bs x) cc); w64 (Spa.u32_at (hx_bs x) (cc + 4));
 w64 ((hx_P x + r + 8) mod 8 + 3); w64 rf; w64 (hx_P x + r + 16)].

Lemma pbW_walk_entry : forall F fc (x : pctx) r cc n ko cl keys rf regs mem md hi23 rs,
call_ok B x -> WALK_at B x r cc n ko cl keys rf F fc regs mem md -> hx_P x + cc <= hi23 ->
regions_wf (hk_saves :: hk_temps (pbW_tcs 50) :: rs) = true ->
Forall (region_ok rsegs (hk_env x regs (pbW_LW x r cc rf)) (hx_rd x mem)) rs ->
pairwise_disjoint (hk_env x regs (pbW_LW x r cc rf)) (hk_saves :: hk_temps (pbW_tcs 50) :: rs) ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs (pbW_LW x r cc rf)) (pbW_ssW (pbW_fW hi23) rs)
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_WALK) mem (seg_rom rsegs))).
Proof.
intros F fc x r cc n ko cl keys rf regs mem md hi23 rs Hc HWk H23 Hwf Hrs Hpd.
pose proof HWk as (HC & Hfx & HM & HL & (R14 & R16) & R23 & R24 & R25).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as RTY.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
set (L := pbW_LW x r cc rf).
unfold pbW_ssW. apply (pbW_entry F fc x PAT_KEY cl _ regs mem md L PC_WALK _ _ _ _ Hc HC); [ | exact Hwf | | exact Hrs | exact Hpd | ].
- apply regs_ok_pin; [unfold hk_env; apply regs_ok_Ereg | pbW_ne0 |].
  rewrite denot_lit_U. unfold pbW_s5e. rewrite (hgw_U_shadow _ 22 (hx_P x + r + 8)); [exact L21 | | | lia].
  + apply U_atom; [rewrite (hk_env_reg x regs L 22 22%bv eq_refl); exact L22 | lia].
  + apply U_atom; [rewrite (hk_env_reg x regs L 27 27%bv eq_refl); exact C27 | unfold SHADOW_OFF; lia].
- apply (pbW_tcs_ok x regs mem L r cl rf 50 HL);
  [exact (hk_env_seg x regs L 3) | exact (hk_env_seg x regs L 4) | exact (hk_env_seg x regs L 5) | lia | lia | lia].
- assert (A14 : ew (hk_env x regs L) 14 = w64 (hx_P x + r + 16)) by (rewrite (hk_env_reg x regs L 14 14%bv eq_refl); exact R14).
  assert (A16 : ew (hk_env x regs L) 16 = w64 8) by (rewrite (hk_env_reg x regs L 16 16%bv eq_refl); exact R16).
  assert (A22 : ew (hk_env x regs L) 22 = w64 (hx_P x + r + 8)) by (rewrite (hk_env_reg x regs L 22 22%bv eq_refl); exact L22).
  assert (A23 : ew (hk_env x regs L) 23 = w64 (hx_P x + cc)) by (rewrite (hk_env_reg x regs L 23 23%bv eq_refl); exact R23).
  assert (A47 : ew (hk_env x regs L) 47 = w64 (Spa.u32_at (hx_bs x) (r + 8))) by exact (hk_env_seg x regs L 0).
  assert (A48 : ew (hk_env x regs L) 48 = w64 (Spa.u32_at (hx_bs x) cc)) by exact (hk_env_seg x regs L 1).
  assert (A49 : ew (hk_env x regs L) 49 = w64 (Spa.u32_at (hx_bs x) (cc + 4))) by exact (hk_env_seg x regs L 2).
  cbn [atoms_ok pbW_fW]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite A14, A16, A22, A23, A47, A48, A49, !unsigned_lit_small by lia.
  change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
  repeat split; try lia; clear - HP16 Hc8 Hr8; Z.div_mod_to_equations; lia.
Qed.

Theorem segWALK_ok : segWALK_stmt B MT.
Proof.
unfold segWALK_stmt. intros x r cc n ko cl keys rf Hc HADV HKEY HEXIT F fc regs mem md HWk.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsl.
pose proof HWk as (HC & Hfx & HM & HL & (R14 & R16) & R23 & R24 & R25).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_pod_at_cut B pb_segs_low x PAT_KEY cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
pose proof (hk_pod_side B x Hc Hnull) as Hside.
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as RTY.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof alloc_ceiling_value as [[AC1 AC2] _]. pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
assert (Hsh : forall a, 0 <= a <= 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
assert (Hcc : cc <= hx_len x) by (clear - Hc8 Hl8m Hrl Hc1 Hr8; unfold hx_len in *; Z.div_mod_to_equations; lia).
set (L := pbW_LW x r cc rf).
set (E0 := hk_env x regs L).
assert (EG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> ew E0 n = w64 v).
{ intros n0 rg v Hn0 Hv. subst E0. rewrite (hk_env_reg x regs L n0 rg Hn0). exact Hv. }
assert (UG : forall (n : nat) (rg : bv 5) v, Z.of_nat n = bv_unsigned rg -> getr regs rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff n 0) = v) by (intros n0 rg v Hn0 Hv Hr; apply U_atom; [exact (EG n0 rg v Hn0 Hv) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v Hv Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl C2); apply unsigned_lit_small; lia).
assert (E22 : ew E0 22 = w64 (hx_P x + r + 8)) by exact (EG 22%nat 22%bv _ eq_refl L22).
assert (E22' : ew E0 22 = w64 (hx_P x + (r + 8))) by (rewrite E22; f_equal; lia).
assert (E23 : ew E0 23 = w64 (hx_P x + cc)) by exact (EG 23%nat 23%bv _ eq_refl R23).
assert (E27 : ew E0 27 = w64 SHADOW_OFF) by exact (EG 27%nat 27%bv _ eq_refl C27).
assert (U14 : U E0 (SOff 14 0) = hx_P x + r + 16) by (apply (UG 14%nat 14%bv); [reflexivity | exact R14 | lia]).
assert (U16 : U E0 (SOff 16 0) = 8) by (apply (UG 16%nat 16%bv); [reflexivity | exact R16 | lia]).
assert (U22 : U E0 (SOff 22 0) = hx_P x + r + 8) by (apply (UG 22%nat 22%bv); [reflexivity | exact L22 | lia]).
assert (U23 : U E0 (SOff 23 0) = hx_P x + cc) by (apply (UG 23%nat 23%bv); [reflexivity | exact R23 | lia]).
assert (U27 : U E0 (SOff 27 0) = SHADOW_OFF) by (apply U_atom; [exact E27 | unfold SHADOW_OFF; lia]).
assert (U21 : U E0 pbW_s5e = shadow_addr (hx_P x + r + 8))
by (apply hgw_U_shadow; [exact U22 | exact U27 | unfold hx_len in *; lia]).
assert (U47 : U E0 (SOff 47 0) = Spa.u32_at (hx_bs x) (r + 8)) by (apply (UL 0%nat); [reflexivity | lia]).
assert (U48 : U E0 (SOff 48 0) = Spa.u32_at (hx_bs x) cc) by (apply (UL 1%nat); [reflexivity | lia]).
assert (U49 : U E0 (SOff 49 0) = Spa.u32_at (hx_bs x) (cc + 4)) by (apply (UL 2%nat); [reflexivity | lia]).
assert (Hs6 : region_ok rsegs E0 (hx_rd x mem) pbW_s6r).
{ unfold region_ok, pbW_s6r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E0.
  rewrite E22, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 47 0) (Spa.u32_at (hx_bs x) (r + 8)));
  [rewrite hk_sv_SOff0; exact (hk_env_seg x regs L 0) | cbn; lia | lia |].
  rewrite Z.add_0_r. replace (hx_P x + r + 8) with (hx_P x + (r + 8)) by lia.
  apply hgw_pod_u32; [exact HG | lia | unfold hx_len in *; lia]. }
assert (SH22 : shent_ok rsegs hk_Bx E0 (hx_rd x mem) (mkSHE 22 0 8))
by exact (hk_shent_pod B x (w_H (hx_W x)) mem E0 22 (r + 8) 0 8 Hc Hnull E27 E22' HRA ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold hx_len in *; lia)).
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 53 E0 E0) by apply env_agree_refl.
unfold cfg_at. change (w64 PC_WALK) with (Z_to_bv 64 PC_WALK).
destruct (Z_le_gt_dec (cc + 8) (r + 16 + Spa.u32_at (hx_bs x) (r + 8))) as [HA|HBc].
{ (* ---- case A: the child's header lies in the Struct body ---- *)
assert (Hs7 : region_ok rsegs E0 (hx_rd x mem) pbW_s7r).
{ unfold region_ok, pbW_s7r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E0.
  rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 48 0) (Spa.u32_at (hx_bs x) cc));
    [rewrite hk_sv_SOff0; exact (hk_env_seg x regs L 1) | cbn; lia | lia |].
    rewrite Z.add_0_r. apply hgw_pod_u32; [exact HG | lia | unfold hx_len in *; lia].
  - apply (chunk_ok_val rsegs _ _ _ 4 4 (SOff 49 0) (Spa.u32_at (hx_bs x) (cc + 4)));
    [rewrite hk_sv_SOff0; exact (hk_env_seg x regs L 2) | cbn; lia | lia |].
    replace (hx_P x + cc + 4) with (hx_P x + (cc + 4)) by lia.
    apply hgw_pod_u32; [exact HG | lia | unfold hx_len in *; lia]. }
assert (SH23 : shent_ok rsegs hk_Bx E0 (hx_rd x mem) (mkSHE 23 0 8))
by exact (hk_shent_pod B x (w_H (hx_W x)) mem E0 23 cc 0 8 Hc Hnull E27 E23 HRA ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold hx_len in *; lia)).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 (pbW_ssW (pbW_fW (2 ^ 47 - 16)) [pbW_s6r; pbW_s7r])
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_WALK) mem (seg_rom rsegs)))).
{ apply (pbW_walk_entry F fc x r cc (S n) ko cl keys rf regs mem md (2 ^ 47 - 16) [pbW_s6r; pbW_s7r] Hc HWk
    ltac:(unfold hx_len in *; lia)
    ltac:(vm_compute; reflexivity) (@Forall_cons _ _ _ _ Hs6 (@Forall_cons _ _ _ _ Hs7 (@Forall_nil _ _)))).
  apply pairwise_disjoint_of_extents. unfold hk_saves, hk_temps, pbW_s6r, pbW_s7r.
  cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold L. fold E0.
  rewrite (EG 2%nat 2%bv _ eq_refl C2), (EG 8%nat 8%bv _ eq_refl C8), E22, E23, !unsigned_lit_small
    by (unfold hx_sp, hx_len in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold hx_sp, hx_len, T_parse_STK, T_PARSE_FRAME, ESTACK in *. destruct Hside; repeat split; lia. }
assert (SHOK : sh_ok rsegs hk_Bx [mkSHE 22 0 8; mkSHE 23 0 8] E0 (hx_rd x mem))
by exact (@Forall_cons _ _ _ _ SH22 (@Forall_cons _ _ _ _ SH23 (@Forall_nil _ _))).
(* 0x84cb4 .. 0x84cbc: bltu s7,a4 (never: cc >= r + 16) *)
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB1.
{ exfalso. rewrite U23, U14 in HB1. apply Z.ltb_lt in HB1. lia. }
(* 0x84cc4: bltu VS,8 (never in case A) *)
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB2.
{ exfalso. rewrite U47, U16 in HB2. apply Z.ltb_lt in HB2. lia. }
rewrite U47, U16 in HB2. apply Z.ltb_ge in HB2.
(* 0x84cd0: bltu VS - 8, cc - (r + 16) (never in case A) *)
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB3.
{ exfalso. rewrite (hgw_U_off E0 47 _ (-8) U47 ltac:(lia)), (hgw_U_subba E0 14 23 _ _ U14 U23 ltac:(lia)) in HB3.
  apply Z.ltb_lt in HB3. lia. }
(* 0x84cd4 .. 0x84cf4: the check of s7, CS = lwu s7; bltu r + 8 + VS - cc, CS: spa_pod_is_inside *)
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB4;
rewrite (hgw_U_rest E0 22 23 47 _ _ _ U22 U23 U47 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), U48 in HB4.
{ (* not inside: EXIT 0x85218 *)
  apply Z.ltb_lt in HB4.
  pbW_run_to x Hc HAE KM Hio U2 PC_EXIT.
  eapply (pbW_exit_exit F fc x r cc n ko cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 51 0) Hc HWk HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia)) | pbW_k25 HAE R25 | pbW_in | exact U2 | pbW_in
  | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia))
  | rewrite (pbW_inside_A x r cc ltac:(lia) Hc8 ltac:(unfold hp_vs; lia)); apply Z.leb_gt; unfold hp_vs; lia
  | exact HJ | exact Hio | exact KM | exact HEXIT ]. }
apply Z.ltb_ge in HB4.
assert (Hci : hp_child_in x r cc).
{ unfold hp_child_in. rewrite (pbW_inside_A x r cc ltac:(lia) Hc8 ltac:(unfold hp_vs; lia)). apply Z.leb_le.
  unfold hp_vs; lia. }
assert (U17 : U E0 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 27 0)) = shadow_addr (hx_P x + cc))
by (apply hgw_U_shadow; [exact U23 | exact U27 | unfold hx_len in *; lia]).
(* 0x84cf8: bnez s8 *)
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB5; rewrite U_lit in HB5 by lia.
- (* the pending key: strncmp (0x84d80 .. 0x84d94 jal 0x41c24) *)
  destruct ko as [ck|].
  2:{ exfalso. change (hp_keyv x None) with 0 in R24. rewrite (UG 24%nat 24%bv _ eq_refl R24 ltac:(lia)) in HB5.
      cbn in HB5. discriminate HB5. }
  pose proof (HK ck eq_refl) as HKo. pose proof (hgw_key_bytes x ck HKo) as (_ & Hkb1 & Hkb2 & _).
  pose proof HKo as (Hck0 & _).
  change (hp_keyv x (Some ck)) with (hx_P x + ck + 8) in R24.
  pbW_run_to x Hc HAE KM Hio U2 B_TRAMP_STRNCMP.
  lazymatch goal with HS' : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg ?ms ?md2) _ =>
    rewrite (pbW_cfg_stop F fc E ss ms _ B_TRAMP_STRNCMP md2 HS' ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
    refine (pbW_call x r cc n ck cl keys rf F fc (ms_regs ms) (ms_mem ms) md2 Hc
      (pbW_stop F fc x PAT_KEY cl _ regs mem md L E ss ms md2 53 Hc HC ltac:(lia) eq_refl HS' HAE ltac:(lia)
        ltac:(pbW_fixed_tac) HJ Hio KM)
      Hfx HM Hci _ _ _ _ _ _ _ _ _ (pbW_ret_ok x r cc n ck cl keys rf Hc HADV (HKEY ck eq_refl)))
  end.
  + unfold pb_loop. split; [pbW_greg HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))|].
    split; [pbW_greg HAE U21|].
    split; [pbW_greg HAE (UG 22%nat 22%bv _ eq_refl L22 ltac:(lia))|].
    split; [pbW_tval 1%nat 16 HAE U2; pbW_uat HAE (UL 3%nat _ eq_refl ltac:(lia))|].
    split; [pbW_tval 1%nat 32 HAE U2; pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia))|].
    pbW_tval 1%nat 40 HAE U2; pbW_uat HAE (UL 5%nat _ eq_refl ltac:(lia)).
  + pbW_greg HAE U23.
  + pbW_greg HAE (UG 24%nat 24%bv _ eq_refl R24 ltac:(unfold hx_len in *; lia)).
  + pbW_k25 HAE R25.
  + pbW_greg HAE (UG 24%nat 24%bv _ eq_refl R24 ltac:(unfold hx_len in *; lia)).
  + pbW_glit HAE.
  + pbW_glit HAE.
  + pbW_glit HAE.
  + pbW_tval 1%nat 48 HAE U2. pbW_uat HAE U17.
- (* no pending key *)
  destruct ko as [ck|].
  { exfalso. pose proof (HK ck eq_refl) as (Hck0 & _). pose proof (hgw_key_bytes x ck (HK ck eq_refl)) as (_ & _ & Hkb2 & _).
    pose proof (hgw_u32_range (hx_bs x) ck) as RCK.
    change (hp_keyv x (Some ck)) with (hx_P x + ck + 8) in R24.
    rewrite (UG 24%nat 24%bv _ eq_refl R24 ltac:(unfold hx_len in *; lia)) in HB5.
    destruct (Z.eqb_spec (hx_P x + ck + 8) 0); [lia | discriminate HB5]. }
  (* 0x84cfc .. 0x84d0c: the check of s7, CS >> 20 *)
  pbW_run x Hc HAE KM Hio U2.
  pbW_branch HAE HB6; rewrite (pbW_U_srl20 E0 48 _ U48 RCS), U_lit in HB6 by lia.
  { (* CS >= 2^20: s8 = 0, ADV *)
    apply negb_true_iff, Z.eqb_neq in HB6.
    assert (Hbig : 2 ^ 20 <= Spa.u32_at (hx_bs x) cc).
    { destruct (Z_lt_le_dec (Spa.u32_at (hx_bs x) cc) (2 ^ 20)) as [Hl|Hl]; [|exact Hl].
      exfalso. apply HB6. apply Z.div_small. lia. }
    assert (Hko : hgw_ko x cc = None) by (apply pbW_ko_none; [lia | left; exact Hbig]).
    pbW_run_to x Hc HAE KM Hio U2 PC_ADV.
    eapply (pbW_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 50 0)
      (SOff 51 0) (SOff 52 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hci) HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
    | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbW_ukept HAE U21
    | pbW_ukept HAE U22 | pbW_ukept HAE U14 | pbW_ukept HAE U16 | pbW_ukept HAE U23
    | pbW_ureg HAE; rewrite U_lit by lia; rewrite Hko; reflexivity
    | pbW_k25 HAE R25 | pbW_ukept HAE U17
    | pbW_in | exact U2
    | pbW_in | pbW_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbW_in | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia))
    | pbW_in | pbW_uat HAE (UL 5%nat _ eq_refl ltac:(lia))
    | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ]. }
  apply negb_false_iff, Z.eqb_eq in HB6.
  assert (Hsmall : Spa.u32_at (hx_bs x) cc < 2 ^ 20).
  { destruct (Z_lt_le_dec (Spa.u32_at (hx_bs x) cc) (2 ^ 20)) as [Hl|Hl]; [exact Hl|].
    exfalso. pose proof (Z.div_le_mono (2 ^ 20) (Spa.u32_at (hx_bs x) cc) (2 ^ 20) ltac:(lia) Hl) as Hd.
    rewrite Z.div_same in Hd by lia. lia. }
  (* 0x84d10 .. 0x84d28: the check of s7 + 4; s8 = 0; beqz CS *)
  pbW_run x Hc HAE KM Hio U2.
  pbW_branch HAE HB7; rewrite U48, U_lit in HB7 by lia.
  { (* CS = 0: ADV *)
    apply Z.eqb_eq in HB7.
    assert (Hko : hgw_ko x cc = None) by (apply pbW_ko_none; [lia | right; left; exact HB7]).
    pbW_run_to x Hc HAE KM Hio U2 PC_ADV.
    eapply (pbW_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 50 0)
      (SOff 51 0) (SOff 52 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hci) HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
    | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbW_ukept HAE U21
    | pbW_ukept HAE U22 | pbW_ukept HAE U14 | pbW_ukept HAE U16 | pbW_ukept HAE U23
    | pbW_ureg HAE; rewrite U_lit by lia; rewrite Hko; reflexivity
    | pbW_k25 HAE R25 | pbW_ukept HAE U17
    | pbW_in | exact U2
    | pbW_in | pbW_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbW_in | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia))
    | pbW_in | pbW_uat HAE (UL 5%nat _ eq_refl ltac:(lia))
    | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ]. }
  apply Z.eqb_neq in HB7.
  (* 0x84d2c .. 0x84d30: lw type; bne type,8 *)
  pbW_run x Hc HAE KM Hio U2.
  pbW_branch HAE HB8; rewrite U16, (hgw_U_sext32_eqb E0 49 _ 8 U49 RTY ltac:(lia)) in HB8.
  { (* type <> String: ADV *)
    apply negb_true_iff, Z.eqb_neq in HB8.
    assert (Hko : hgw_ko x cc = None) by (apply pbW_ko_none; [lia | right; right; exact HB8]).
    pbW_run_to x Hc HAE KM Hio U2 PC_ADV.
    eapply (pbW_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 50 0)
      (SOff 51 0) (SOff 52 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hci) HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
    | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
    | pbW_ukept HAE U21
    | pbW_ukept HAE U22 | pbW_ukept HAE U14 | pbW_ukept HAE U16 | pbW_ukept HAE U23
    | pbW_ureg HAE; rewrite U_lit by lia; rewrite Hko; reflexivity
    | pbW_k25 HAE R25 | pbW_ukept HAE U17
    | pbW_in | exact U2
    | pbW_in | pbW_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
    | pbW_in | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia))
    | pbW_in | pbW_uat HAE (UL 5%nat _ eq_refl ltac:(lia))
    | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ]. }
  apply negb_false_iff, Z.eqb_eq in HB8.
  assert (Ua0 : U E0 (SAlu ALU_ADD (SOff 23 8) (SAluw ALU_ADD (SOff 48 0) (SLit (-1)))) =
    hx_P x + cc + 8 + Spa.u32_at (hx_bs x) cc - 1)
  by (apply pbW_U_last; [exact U23 | exact U48 | lia | lia | unfold hx_len in *; lia]).
  assert (Ua1 : U E0 (SOff 23 8) = hx_P x + cc + 8) by (apply (hgw_U_off E0 23); [exact U23 | unfold hx_len in *; lia]).
  (* 0x84d34 .. 0x84d40: a1 = s7 + 8, a0 = a1 + (CS - 1); bltu a0,a1 (trap, never) *)
  pbW_run x Hc HAE KM Hio U2.
  pbW_branch HAE HB9.
  { exfalso. rewrite Ua0, Ua1 in HB9. apply Z.ltb_lt in HB9. lia. }
  (* 0x84d44 .. 0x84d50: the null test of the end pointer (trap, never) *)
  pbW_run x Hc HAE KM Hio U2.
  pbW_branch HAE HB10.
  { exfalso. rewrite (pbW_U_nz E0 _ ltac:(rewrite Ua0; unfold hx_len in *; lia)), U_lit in HB10 by lia.
    cbn in HB10. discriminate HB10. }
  (* to the last body byte's check: WLB 0x84d54 *)
  pbW_run_to x Hc HAE KM Hio U2 PC_WLB.
  eapply (pbW_exit_wlb F fc x r cc n cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 50 0) (SOff 51 0)
    (SOff 52 0) Hc HC Hfx HM Hci ltac:(lia) HB8 HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia))
  | pbW_ukept HAE U21
  | pbW_ukept HAE U22 | pbW_ukept HAE U14 | pbW_ukept HAE U16 | pbW_ukept HAE U23
  | pbW_ureg HAE; rewrite U_lit by lia; reflexivity
  | pbW_k25 HAE R25 | pbW_ukept HAE U17 | pbW_ukept HAE Ua0 | pbW_ukept HAE Ua1
  | pbW_in | exact U2
  | pbW_in | pbW_uat HAE (UL 3%nat _ eq_refl ltac:(lia))
  | pbW_in | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia))
  | pbW_in | pbW_uat HAE (UL 5%nat _ eq_refl ltac:(lia))
  | exact HJ | exact Hio | exact KM | exact (pbW_lb_ok x r cc n cl keys rf Hc HADV) ]. }
(* ---- case B: the child's header does not lie in the Struct body: the walk ends before s7's check ---- *)
assert (Hout : Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false)
by (apply pbW_out_B; [lia | exact Hc8 | unfold hp_vs; lia]).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 (pbW_ssW (pbW_fW (2 ^ 47 - 8)) [pbW_s6r])
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_WALK) mem (seg_rom rsegs)))).
{ apply (pbW_walk_entry F fc x r cc (S n) ko cl keys rf regs mem md (2 ^ 47 - 8) [pbW_s6r] Hc HWk
    ltac:(unfold hx_len in *; lia)
    ltac:(vm_compute; reflexivity) (@Forall_cons _ _ _ _ Hs6 (@Forall_nil _ _))).
  apply pairwise_disjoint_of_extents. unfold hk_saves, hk_temps, pbW_s6r.
  cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold L. fold E0.
  rewrite (EG 2%nat 2%bv _ eq_refl C2), (EG 8%nat 8%bv _ eq_refl C8), E22, !unsigned_lit_small
    by (unfold hx_sp, hx_len in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold hx_sp, hx_len, T_parse_STK, T_PARSE_FRAME, ESTACK in *. destruct Hside; repeat split; lia. }
assert (SHOK : sh_ok rsegs hk_Bx [mkSHE 22 0 8] E0 (hx_rd x mem)) by exact (@Forall_cons _ _ _ _ SH22 (@Forall_nil _ _)).
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB1.
{ pbW_run_to x Hc HAE KM Hio U2 PC_EXIT.
  eapply (pbW_exit_exit F fc x r cc n ko cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 51 0) Hc HWk HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia)) | pbW_k25 HAE R25 | pbW_in | exact U2 | pbW_in
  | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia)) | exact Hout | exact HJ | exact Hio | exact KM | exact HEXIT ]. }
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB2.
{ pbW_run_to x Hc HAE KM Hio U2 PC_EXIT.
  eapply (pbW_exit_exit F fc x r cc n ko cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 51 0) Hc HWk HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia)) | pbW_k25 HAE R25 | pbW_in | exact U2 | pbW_in
  | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia)) | exact Hout | exact HJ | exact Hio | exact KM | exact HEXIT ]. }
rewrite U47, U16 in HB2. apply Z.ltb_ge in HB2.
pbW_run x Hc HAE KM Hio U2.
pbW_branch HAE HB3.
{ pbW_run_to x Hc HAE KM Hio U2 PC_EXIT.
  eapply (pbW_exit_exit F fc x r cc n ko cl keys rf regs mem md L _ _ _ _ 53 (pbW_tcs 50) (SOff 51 0) Hc HWk HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | pbW_fixed_tac
  | pbW_ukept HAE (UG 20%nat 20%bv _ eq_refl L20 ltac:(lia)) | pbW_k25 HAE R25 | pbW_in | exact U2 | pbW_in
  | pbW_uat HAE (UL 4%nat _ eq_refl ltac:(lia)) | exact Hout | exact HJ | exact Hio | exact KM | exact HEXIT ]. }
exfalso. rewrite (hgw_U_off E0 47 _ (-8) U47 ltac:(lia)), (hgw_U_subba E0 14 23 _ _ U14 U23 ltac:(lia)) in HB3.
apply Z.ltb_ge in HB3. lia.
Qed.

End w.

Print Assumptions segWALK_ok.
Print Assumptions segADV_ok.
