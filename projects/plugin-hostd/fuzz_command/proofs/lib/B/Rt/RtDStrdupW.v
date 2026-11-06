(* Facts the composition of plugin-hostd/fuzz_command's strdup entry (RtDStrdupX.v) uses between its stretches:
   the caller's frame chain kept by the entry's writes, the input/output state kept by the model, the parity of a
   return address, and the memory the entry leaves after its copy (musl memcpy's bytes written into the new block
   through the restricted memory) with the allocator invariant kept over it. The text of lib/A/Rt/RtDStrdupW.v with
   module paths lib/A to lib/B, for the ASan+UBSan image (fuzz_command.asan-ubsan); it names no address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YK0u.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import
RtDefs RtString RtAlloc RtAPI RtDDefs RtSRegionDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the caller's frame chain reads only above the entry's own window, so the entry's writes keep it *)
Lemma fpchain_frame : forall ch (rd1 rd2 : Z -> option Z) (lo bp top : Z),
(forall a, lo <= a -> a <= top -> rd2 a = rd1 a) -> lo + 16 <= bp -> bp <= top ->
fpchain rd1 bp top ch -> fpchain rd2 bp top ch.
Proof.
induction ch as [|[[fp ra] nfp] ch IH]; intros rd1 rd2 lo bp top Hag Hbp Hbt H; cbn in *.
- destruct H as (r & Hr & Hb). exists r. split; [rewrite Hag by lia; exact Hr | exact Hb].
- destruct H as (Hfp & Hm8 & H8 & H16 & Hra & Hrest). subst fp.
split; [reflexivity|]. split; [exact Hm8|].
split; [rewrite Hag by lia; exact H8|]. split; [rewrite Hag by lia; exact H16|].
split; [exact Hra|].
destruct (bad_next bp top nfp) eqn:Hbad; [exact Hrest|].
unfold bad_next in Hbad. apply orb_false_elim in Hbad as [Hb1 _]. apply orb_false_elim in Hb1 as [Hb11 Hb12].
apply Z.leb_gt in Hb11. apply Z.leb_gt in Hb12.
apply (IH rd1 rd2 lo nfp top Hag ltac:(lia) ltac:(lia) Hrest).
Qed.

(* one eight-byte read is kept when its eight bytes are kept *)
Lemma rdword_frame : forall (H : word -> bool) (m1 m2 : word -> option byte) (a : Z),
(forall k, 0 <= k < 8 -> aview tfibsegs H m2 (a + k) = aview tfibsegs H m1 (a + k)) ->
rdword (aview tfibsegs H m2) a = rdword (aview tfibsegs H m1) a.
Proof.
intros H m1 m2 a E. unfold rdword.
pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
rewrite E0. rewrite (E 1 ltac:(lia)). rewrite (E 2 ltac:(lia)). rewrite (E 3 ltac:(lia)).
rewrite (E 4 ltac:(lia)). rewrite (E 5 ltac:(lia)). rewrite (E 6 ltac:(lia)). rewrite (E 7 ltac:(lia)).
reflexivity.
Qed.

(* the model only materializes along the whole walk, so the input and output state never moves *)
Lemma sbm_same_io : forall (md md' : Model), same_but_materialized md md' -> same_io md md'.
Proof.
intros md md' H. unfold same_io. rewrite (same_but_materialized_wvb md md' H).
destruct md as [fd [maps lazy mat] io fs proc lim tm]. cbn. repeat split; reflexivity.
Qed.

Lemma same_io_trans : forall (m1 m2 m3 : Model), same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof.
intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
split; [rewrite B1; exact A1|]. split; [rewrite B2; exact A2|].
split; [rewrite B3; exact A3 | rewrite B4; exact A4].
Qed.

(* a return address the entry may jump back to is even *)
Lemma ret_ok_mod2 : forall k, YK0s.ret_ok k -> bv_unsigned k mod 2 = 0.
Proof.
intros k H. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
remember (Z.land (bv_unsigned k) (-2)) as z eqn:Ez.
assert (Hz : z mod 2 = 0).
{ rewrite Ez. change (Z.land (bv_unsigned k) (-2) mod 2 = 0) with (Z.land (bv_unsigned k) (-2) mod 2 ^ 1 = 0).
rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
change (Z.land (-2) (Z.ones 1)) with 0. apply Z.land_0_r. }
rewrite <- H. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
pose proof (Z.div_mod z 18446744073709551616 ltac:(lia)) as D.
replace (z mod 18446744073709551616) with (z + (- 9223372036854775808 * (z / 18446744073709551616)) * 2) by lia.
rewrite Z_mod_plus_full. exact Hz.
Qed.

(* The memory after the copy: [bs] written at [d] through the restricted memory, the hidden bytes put back. *)
Lemma aview_wr_out : forall (H : word -> bool) (m : word -> option byte) (d : Z) (bs : list byte) (a : Z),
0 <= d < 2 ^ 64 -> d + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length bs)) ->
aview tfibsegs H (munrestrict H m (wbytes (mrestrict H m) (Z_to_bv 64 d) bs)) a = aview tfibsegs H m a.
Proof.
intros H m d bs a Hd Hnw Ha Hout.
unfold aview, mbyte, munrestrict, mrestrict.
destruct (H (Z_to_bv 64 a)) eqn:Eh; [reflexivity|].
rewrite YK0u.wbytes_outside.
- cbv beta. rewrite Eh. reflexivity.
- rewrite unsigned_lit_small by lia. exact Hnw.
- rewrite !unsigned_lit_small by lia. lia.
Qed.

Lemma aview_wr_in : forall (H : word -> bool) (m : word -> option byte) (d : Z) (bs : list byte) (i : nat),
0 <= d < 2 ^ 64 -> d + Z.of_nat (length bs) <= 2 ^ 64 -> (i < length bs)%nat -> H (Z_to_bv 64 (d + Z.of_nat i)) = false ->
aview tfibsegs H (munrestrict H m (wbytes (mrestrict H m) (Z_to_bv 64 d) bs)) (d + Z.of_nat i) =
Some (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof.
intros H m d bs i Hd Hnw Hi Hh.
unfold aview, mbyte, munrestrict, mrestrict. rewrite Hh.
rewrite YK0u.wbytes_inside.
- rewrite !unsigned_lit_small by lia.
replace (d + Z.of_nat i - d) with (Z.of_nat i) by lia. rewrite Nat2Z.id. reflexivity.
- rewrite unsigned_lit_small by lia. exact Hnw.
- rewrite !unsigned_lit_small by lia. lia.
Qed.

(* The allocator invariant survives the copy: every byte written is a byte of a block the client owns. *)
Lemma AR_wr : forall B, AR_laws tfibsegs B ->
forall ly S (W : world tfibsegs) (mem : word -> option byte) (md md' : Model) (d : Z) (bs : list byte),
AR tfibsegs B ly S W mem md -> 0 <= d < 2 ^ 64 -> d + Z.of_nat (length bs) <= 2 ^ 64 ->
(forall a, d <= a < d + Z.of_nat (length bs) -> apresent (w_H W) mem a /\ ~ aowned B ly S a) ->
same_but_materialized md md' ->
AR tfibsegs B ly S W (munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 d) bs)) md'.
Proof.
intros B LAWS ly S W mem md md' d bs HAR Hd Hnw Hblk SBM.
destruct (same_but_materialized_frame md md' SBM) as (_ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3).
apply (al_frame _ _ LAWS ly S W mem md _ md' HAR).
- intros a Ha Hown. apply aview_wr_out; [exact Hd | exact Hnw | exact Ha |].
intros Hin. exact (proj2 (Hblk a Hin) Hown).
- intros a Hv. rewrite (YE2y.aview_mod (w_H W) _ a). rewrite (YE2y.aview_mod (w_H W) mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' d) as [L1|L1]; [rewrite aview_wr_out by lia; exact Hv|].
destruct (Z_lt_le_dec a' (d + Z.of_nat (length bs))) as [L2|L2]; [|rewrite aview_wr_out by lia; exact Hv].
replace a' with (d + Z.of_nat (Z.to_nat (a' - d))) by lia.
rewrite aview_wr_in; [discriminate | exact Hd | exact Hnw | lia |].
exact (proj1 (proj1 (Hblk (d + Z.of_nat (Z.to_nat (a' - d))) ltac:(lia)))).
- exact V1.
- exact V2.
- exact V3.
- intros a _ Hh. unfold munrestrict. rewrite Hh. reflexivity.
Qed.

End w.
