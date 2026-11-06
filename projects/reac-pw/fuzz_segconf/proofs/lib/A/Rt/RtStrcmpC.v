(* The strcmp contract of lib/A/Rt/RtString.v (astrcmp_realizes, window 2 * ESTACK) at PC_strcmp = 0x4513c, the
   one-instruction trampoline `j 0x45a24` of ___interceptor_strcmp. Proved input: lib/A/Rt/RtStrcmp.v
   cmd_strcmp_tramp, fuzz_grant's walk of the whole interceptor (proofs/libreac/fuzz_grant/lib/A/Rt/Strcmp.v)
   relocated to this image, which states the shared form lib/Reusable/AStrcmpDef.v astrcmp_realizes: the compare
   stops at an index k with c1 = x[k], c2 = y[k], and the entry returns CharCmpX c1 c2 (-1, 0 or 1).
   This file reads the walk's premises off the contract's. The two C strings (astr_at) give the stop index k
   (str_stop: the first index where the bytes differ or s1's byte is the NUL; k <= |sx| and k <= |sy|) and so
   str_meet; aread_ok over |s| + 1 bytes gives, for the k + 1 bytes the checks read, the visible bytes outside the
   window, amem_range, range_addressable and shadow_hull_vis (each holds of a prefix of a range where it holds of
   the range). The return word is 0 exactly when c1 = c2, which is exactly when sx = sy (str_stop). The walk's post
   is art_post's: the scratch window is present after the call because it is present before it (ecall_pre_stk)
   and the walk keeps every present byte present. The contract's atail_vis and rt_rom_view are not used: the
   interceptor reads no byte past the stop index and no read-only byte outside its own cells. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK1a YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtStrcmp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Where strcmp stops on two C strings: the first index k where the bytes of sx ++ [NUL] and sy ++ [NUL] differ
   or the byte of sx ++ [NUL] is the NUL. The bytes before k are equal; the bytes at k are equal exactly when the
   strings are. *)
Lemma str_stop : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
exists kn : nat, (kn <= length sx)%nat /\ (kn <= length sy)%nat /\
(forall j, (j < kn)%nat -> nth j (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = nth j (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) /\
(nth kn (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) <> nth kn (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) \/
 nth kn (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0) /\
(nth kn (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = nth kn (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) <-> sx = sy).
Proof.
induction sx as [|a sx IH]; intros sy Hx Hy.
- exists 0%nat. destruct sy as [|b sy]; cbn [app nth length].
  + split; [lia|]. split; [lia|]. split; [intros j Hj; lia|]. split; [right; reflexivity|].
    split; intros _; reflexivity.
  + split; [lia|]. split; [lia|]. split; [intros j Hj; lia|]. split; [right; reflexivity|].
    split; [intros E; exfalso; apply Hy; left; symmetry; exact E | intros E; discriminate E].
- assert (Hx' : ~ In (Z_to_bv 8 0) sx) by (intros H; apply Hx; right; exact H).
  assert (Ha : a <> Z_to_bv 8 0) by (intros E; apply Hx; left; exact E).
  destruct sy as [|b sy].
  + exists 0%nat. cbn [app nth length].
    split; [lia|]. split; [lia|]. split; [intros j Hj; lia|]. split; [left; exact Ha|].
    split; [intros E; exfalso; exact (Ha E) | intros E; discriminate E].
  + assert (Hy' : ~ In (Z_to_bv 8 0) sy) by (intros H; apply Hy; right; exact H).
    destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned b)) as [Hab|Hab].
    * assert (E : a = b) by (apply bv_eq; exact Hab). subst b.
      destruct (IH sy Hx' Hy') as (k & K1 & K2 & K3 & K4 & K5).
      exists (S k). cbn [app nth length].
      split; [lia|]. split; [lia|]. split.
      -- intros j Hj. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply K3. lia.
      -- split; [exact K4|].
         split; intros H; [f_equal; apply K5; exact H | apply K5; injection H as H; exact H].
    * exists 0%nat. cbn [app nth length].
      split; [lia|]. split; [lia|]. split; [intros j Hj; lia|].
      split; [left; intros E; apply Hab; rewrite E; reflexivity|].
      split; [intros E; exfalso; apply Hab; rewrite E; reflexivity
             | intros E; injection E as E1 E2; exfalso; apply Hab; rewrite E1; reflexivity].
Qed.

(* CharCmpX c1 c2 is the zero word exactly when c1 = c2 (the other values, -1 and 1, are not 0 mod 2^64). *)
Lemma strcmp_res_zero : forall c1 c2, w64 (AStrcmpDef.strcmp_res c1 c2) = w64 0 <-> c1 = c2.
Proof.
intros c1 c2. unfold AStrcmpDef.strcmp_res. destruct (Z.eqb_spec c1 c2) as [E|E].
- split; intros _; [exact E | reflexivity].
- destruct (c1 <? c2); split; intros H.
  + apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
  + exfalso. exact (E H).
  + apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
  + exfalso. exact (E H).
Qed.

Theorem cmd_strcmp : forall (B : asyms), AR_laws tfibsegs B -> SegBSyms B ->
RtString.astrcmp_realizes tfibsegs B PC_strcmp.
Proof.
intros B LAWS TB ly S W regs mem md x y sx sy HPRE G10 G11 Hx Hy HSX HSY HRX HRY _ _ _.
pose proof HPRE as (HEP & Hslo & Hpres).
destruct HRX as (Hx0 & Hxn & Hnx & Hsrcx & Hamx & Hrax & Hhx).
destruct HRY as (Hy0 & Hyn & Hny & Hsrcy & Hamy & Hray & Hhy).
destruct HSX as (HBX & HNX). destruct HSY as (HBY & HNY).
unfold astr_len in *.
destruct (str_stop sx sy HNX HNY) as (kn & K1 & K2 & K3 & K4 & K5).
set (c1 := bv_unsigned (nth kn (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
set (c2 := bv_unsigned (nth kn (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
(* the bytes of the two strings and their NULs *)
assert (RX : forall j, (j <= length sx)%nat ->
aview tfibsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))))
by (intros j Hj; apply HBX; rewrite length_app; cbn [length]; lia).
assert (RY : forall j, (j <= length sy)%nat ->
aview tfibsegs (w_H W) mem (y + Z.of_nat j) = Some (bv_unsigned (nth j (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))))
by (intros j Hj; apply HBY; rewrite length_app; cbn [length]; lia).
(* the stop index of the shared form *)
assert (Hmeet : AStrcmpDef.str_meet tfibsegs W mem x y (Z.of_nat kn) c1 c2).
{ unfold AStrcmpDef.str_meet. split; [lia|]. split.
  - intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))). split; [|split].
    + replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply RX. lia.
    + rewrite (K3 (Z.to_nat i) ltac:(lia)). replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia. apply RY. lia.
    + apply byte_nz_u. rewrite app_nth1 by lia. intros E. apply HNX. rewrite <- E. apply nth_In. lia.
  - split; [exact (RX kn K1)|]. split; [exact (RY kn K2)|].
    destruct K4 as [Hne|H0]; [left | right].
    + intros E. apply Hne. apply bv_eq. exact E.
    + unfold c1. rewrite H0. reflexivity. }
(* the k + 1 bytes the checks read: a prefix of each string's range *)
assert (SX : src_ok tfibsegs W regs mem x (Z.of_nat kn + 1)).
{ intros a Ha. destruct (Hsrcx a ltac:(lia)) as [Hv Hs]. split; [exact Hv|].
  intros Hin. apply Hs. unfold ascratch_stk, ESTACK in *. lia. }
assert (SY : src_ok tfibsegs W regs mem y (Z.of_nat kn + 1)).
{ intros a Ha. destruct (Hsrcy a ltac:(lia)) as [Hv Hs]. split; [exact Hv|].
  intros Hin. apply Hs. unfold ascratch_stk, ESTACK in *. lia. }
assert (BX : forall a, x <= a <= x + Z.of_nat kn -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs))
by (intros a Ha; exact (proj2 (Hsrcx a ltac:(lia)))).
assert (BY : forall a, y <= a <= y + Z.of_nat kn -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs))
by (intros a Ha; exact (proj2 (Hsrcy a ltac:(lia)))).
assert (AMX : amem_range x (Z.of_nat kn + 1)) by (unfold amem_range in *; lia).
assert (AMY : amem_range y (Z.of_nat kn + 1)) by (unfold amem_range in *; lia).
assert (RAX : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat kn + 1))
by (intros z Hz; apply Hrax; lia).
assert (RAY : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y (Z.of_nat kn + 1))
by (intros z Hz; apply Hray; lia).
assert (SH : forall p n m, 0 <= p -> 1 <= m <= n ->
shadow_addr (p + m - 1) / 8 * 8 <= shadow_addr (p + n - 1) / 8 * 8).
{ intros p n m Hp Hm. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (HHX : shadow_hull_vis (aview tfibsegs (w_H W) mem) x (Z.of_nat kn + 1)).
{ intros s Hs. pose proof (SH x (Z.of_nat (length sx) + 1) (Z.of_nat kn + 1) Hx0 ltac:(lia)) as M.
  apply (Hhx ltac:(lia) s). lia. }
assert (HHY : shadow_hull_vis (aview tfibsegs (w_H W) mem) y (Z.of_nat kn + 1)).
{ intros s Hs. pose proof (SH y (Z.of_nat (length sy) + 1) (Z.of_nat kn + 1) Hy0 ltac:(lia)) as M.
  apply (Hhy ltac:(lia) s). lia. }
assert (Hk32 : Z.of_nat kn + 1 < 2 ^ 32) by lia.
assert (Hxk : x + Z.of_nat kn + 1 <= 2 ^ 63) by lia.
assert (Hyk : y + Z.of_nat kn + 1 <= 2 ^ 63) by lia.
change (cfg_at tfibsegs PC_strcmp regs mem md) with (cfg_at tfibsegs RtStrcmp.STRCMP_TRAMP regs mem md).
refine (SRr_mono tfibsegs W (cfg_at tfibsegs RtStrcmp.STRCMP_TRAMP regs mem md) _ _
(RtStrcmp.cmd_strcmp_tramp B LAWS TB ly S W regs mem md x y (Z.of_nat kn) c1 c2 HEP Hslo Hpres G10 G11 Hx Hy
Hk32 Hxk Hyk Hmeet SX SY BX BY AMX AMY RAX HHX RAY HHY) _).
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & HKEEP & Hsbm & A10 & Hfr & Hpres').
unfold art_post. split; [reflexivity|]. exists regs', mem', md'.
split; [exact Hc|]. split; [exact HAR'|]. split; [exact HKEEP|]. split; [exact Hsbm|].
split.
- cbv beta. rewrite A10. split; intros H.
  + apply K5. apply strcmp_res_zero in H. unfold c1, c2 in H. apply bv_eq. exact H.
  + apply strcmp_res_zero. unfold c1, c2. rewrite (proj2 K5 H). reflexivity.
- split; [intros a Ha Hs _; exact (Hfr a Ha Hs)|].
  split; [exact Hpres'|].
  intros a Ha. apply Hpres'. exact (Hpres a Ha).
Qed.

End c.
