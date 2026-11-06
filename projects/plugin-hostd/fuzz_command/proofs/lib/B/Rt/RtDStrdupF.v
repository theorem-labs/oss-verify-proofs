(* The four premises the inline shadow check of plugin-hostd/fuzz_command's strdup entry on its ASan+UBSan image
   takes (RtDStrdupS.v sds_block), read off the range premise the contract gives (aread_ok, RtDefs.v:36): every
   granule strictly inside the range is clean, the last granule's shadow byte allows the last byte of the range, and
   the two 8-byte shadow words the check loads at 0x4cda0 and 0x4cda4 are visible. The proof of
   lib/A/Rt/RtDStrdupF.v moved by the name-keyed A-to-B address map. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0x YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* one visible byte, as the check's byte loads read it *)
Lemma sd_rdn1_of_aview : forall (H : word -> bool) (m : word -> option byte) a v,
aview tfibsegs H m a = Some v ->
exists b : byte, rdn tfibsegs (mrestrict H m) (Z_to_bv 64 a) 1%nat = Some [b] /\ bv_unsigned b = v.
Proof.
intros H m a v Hv. destruct (YE2y.aview_byte_ex H m a v Hv) as (b & Hb & -> & _). exists b. split; [|reflexivity].
apply (proj2 (rdn_mbytes tfibsegs _ 1 a [b])). split; [reflexivity|].
intros i Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. exact Hb.
Qed.

(* eight visible bytes, as the check's two word loads read them *)
Lemma sd_rdn8_of_vis : forall (H : word -> bool) (m : word -> option byte) a,
0 <= a -> a + 8 <= 2 ^ 64 ->
(forall i, 0 <= i < 8 -> aview tfibsegs H m (a + i) <> None) ->
exists bs, rdn tfibsegs (mrestrict H m) (Z_to_bv 64 a) 8%nat = Some bs /\ length bs = 8%nat.
Proof.
intros H m a Ha Ha8 Hv.
destruct (YE2y.rdn_of_vis (mrestrict H m) a 8%nat Ha ltac:(cbn [Z.of_nat]; lia)) as (bs & Hbs & Hlen & _).
- intros i Hi. cbn [Z.of_nat] in Hi. intros Hn. apply (Hv i ltac:(lia)).
unfold aview. rewrite Hn. reflexivity.
- exists bs. split; [exact Hbs | exact Hlen].
Qed.

Section g.
Variables (W : world tfibsegs) (mem : word -> option byte) (x len : Z).
Hypothesis Hx : 0 < x.
Hypothesis Hlen : 0 <= len < 64.
Hypothesis Hxn : x + len + 1 <= 2 ^ 63.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (len + 1).
Hypothesis HHULL : shadow_hull_vis (aview tfibsegs (w_H W) mem) x (len + 1).

Local Notation rd := (aview tfibsegs (w_H W) mem).
Local Notation m8 := (mrestrict (w_H W) mem).

Lemma sd_A_bounds : 0 <= YE2y.SB + x / 8 /\ YE2y.SB + x / 8 <= YE2y.SB + (x + len) / 8 /\
YE2y.SB + (x + len) / 8 + 8 < 2 ^ 64 /\
(YE2y.SB + x / 8) / 8 * 8 = YE2y.SB + x / 8 - (YE2y.SB + x / 8) mod 8 /\
(YE2y.SB + (x + len) / 8) / 8 * 8 = YE2y.SB + (x + len) / 8 - (YE2y.SB + (x + len) / 8) mod 8.
Proof.
unfold YE2y.SB.
assert (D1 : x / 8 <= (x + len) / 8) by (apply Z.div_le_mono; lia).
assert (D2 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (D3 : (x + len) / 8 <= x + len) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_mod (2147483648 + x / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (2147483648 + (x + len) / 8) 8 ltac:(lia)).
repeat split; lia.
Qed.

Lemma sd_granules : forall g, x / 8 <= g < (x + len) / 8 ->
rdn tfibsegs m8 (Z_to_bv 64 (YE2y.SB + g)) 1%nat = Some [Z_to_bv 8 0].
Proof.
intros g Hg.
assert (Hin : x <= 8 * g + 7 < x + (len + 1)).
{ pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (x + len) 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound (x + len) 8 ltac:(lia)) as Ml.
lia. }
pose proof (YE2y.ra_granule_zero rd x (len + 1) g HRA Hin ltac:(lia)) as Hz.
destruct (sd_rdn1_of_aview (w_H W) mem (YE2y.SB + g) 0 Hz) as (b & Hb & Hbv).
replace (Z_to_bv 8 0) with b by (apply bv_eq; rewrite Hbv; reflexivity). exact Hb.
Qed.

Lemma sd_last : exists b : byte, rdn tfibsegs m8 (Z_to_bv 64 (YE2y.SB + (x + len) / 8)) 1%nat = Some [b] /\
(bv_unsigned b = 0 \/ (x + len) mod 8 < bv_unsigned b < 8).
Proof.
destruct (YE2y.ra_last rd x (len + 1) HRA ltac:(lia)) as (b1 & Hb1 & Hok).
replace (x + (len + 1) - 1) with (x + len) in Hb1, Hok by lia.
destruct (sd_rdn1_of_aview (w_H W) mem (YE2y.SB + (x + len) / 8) b1 Hb1) as (b & Hb & Hbv).
exists b. split; [exact Hb|]. unfold saddr_ok in Hok. rewrite Hbv. destruct Hok as [-> | [H1 H2]]; [left; reflexivity | right; lia].
Qed.

Lemma sd_words : (exists bs, rdn tfibsegs m8 (Z_to_bv 64 ((YE2y.SB + x / 8) - (YE2y.SB + x / 8) mod 8)) 8%nat = Some bs /\ length bs = 8%nat)
/\ (exists bs, rdn tfibsegs m8 (Z_to_bv 64 ((YE2y.SB + (x + len) / 8) - (YE2y.SB + (x + len) / 8) mod 8)) 8%nat = Some bs /\ length bs = 8%nat).
Proof.
pose proof sd_A_bounds as (P0 & P1 & P2 & P3 & P4).
assert (Hsh0 : shadow_addr x = YE2y.SB + x / 8) by reflexivity.
assert (Hsh1 : shadow_addr (x + (len + 1) - 1) = YE2y.SB + (x + len) / 8)
by (unfold shadow_addr, YE2y.SB; f_equal; f_equal; lia).
pose proof (Z.mod_pos_bound (YE2y.SB + x / 8) 8 ltac:(lia)) as M0.
pose proof (Z.mod_pos_bound (YE2y.SB + (x + len) / 8) 8 ltac:(lia)) as M1.
split.
- apply sd_rdn8_of_vis; [lia | lia |].
intros i Hi. apply HHULL. rewrite Hsh0, Hsh1, P3, P4. lia.
- apply sd_rdn8_of_vis; [lia | lia |].
intros i Hi. apply HHULL. rewrite Hsh0, Hsh1, P3, P4. lia.
Qed.

End g.
End f.
