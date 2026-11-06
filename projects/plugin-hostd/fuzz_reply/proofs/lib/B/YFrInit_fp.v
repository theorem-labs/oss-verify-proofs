(* Modified by Theorem Labs, 2026-10: new file, the fuzz_reply.asan-ubsan twin of lib/A/AFrInit_fp.v (RelocA-2,
   a working branch 50f0c528115). The cf driver's first-call fact about fuzz_reply's harness
   blocks: when every byte of the 20 program objects reads its start-up value gf_init (B/YD2d_fp.v sPE_gf_start /
   B/YD2e_fp.v PL_gf_start give this at the two first-call sites), the entry's harness blocks are none,
   fr_hblks_b W mem = [] (B/YCfn_cf.v): g_src (0x5d8d40), g_out (0x5d90c0) and g_capout (0x5d90a0) are .bss words
   (B/W_rep.v fr_globals_b; each = A's + 0x580), whose image bytes are 0 (gf_words_zero, vm_compute). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YP09 YI04 YI00 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v W_rep YCfn_cf YD2d_fp.
Import ListNotations.
Open Scope Z_scope.

Lemma gf_words_zero : forall i, 0 <= i < 8 ->
  gf_init (0x5d8d40 + i) = 0 /\ gf_init (0x5d90c0 + i) = 0 /\ gf_init (0x5d90a0 + i) = 0.
Proof.
intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
repeat (destruct Hc as [->|Hc]; [vm_compute; repeat split; reflexivity|]). subst i. vm_compute. repeat split; reflexivity.
Qed.
Lemma gf_words_in : forall i, 0 <= i < 8 ->
  Exists (in_zr (0x5d8d40 + i)) GF_OBJ /\ Exists (in_zr (0x5d90c0 + i)) GF_OBJ /\ Exists (in_zr (0x5d90a0 + i)) GF_OBJ.
Proof.
intros i Hi. rewrite GF_OBJ_val. repeat split; apply Exists_exists.
- exists (0x5d8d40, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
- exists (0x5d90c0, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
- exists (0x5d90a0, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma fr_hblks_init : forall (W : world tfibsegs) (mem : word -> option byte),
  (forall a, Exists (in_zr a) GF_OBJ -> aview tfibsegs (w_H W) mem a = Some (gf_init a)) -> fr_hblks_b W mem = [].
Proof.
intros W mem HG.
assert (E : forall p, (p = 0x5d8d40 \/ p = 0x5d90c0 \/ p = 0x5d90a0) -> forall i, 0 <= i < 8 ->
  aview tfibsegs (w_H W) mem (p + i) = Some 0).
{ intros p Hp i Hi. pose proof (gf_words_zero i Hi) as (Z1 & Z2 & Z3). pose proof (gf_words_in i Hi) as (I1 & I2 & I3).
  destruct Hp as [Hp | [Hp | Hp]]; subst p; rewrite HG by assumption; f_equal; assumption. }
assert (Z0 : forall p, (p = 0x5d8d40 \/ p = 0x5d90c0 \/ p = 0x5d90a0) -> rdword (aview tfibsegs (w_H W) mem) p = Some 0).
{ intros p Hp. unfold rdword.
  pose proof (E p Hp 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
  rewrite E0, (E p Hp 1 ltac:(lia)), (E p Hp 2 ltac:(lia)), (E p Hp 3 ltac:(lia)), (E p Hp 4 ltac:(lia)),
    (E p Hp 5 ltac:(lia)), (E p Hp 6 ltac:(lia)), (E p Hp 7 ltac:(lia)). reflexivity. }
unfold fr_hblks_b. cbn [rg_src rg_out rg_capout fr_globals_b].
rewrite (Z0 0x5d8d40), (Z0 0x5d90c0), (Z0 0x5d90a0) by tauto. reflexivity.
Qed.
(* and g_capout reads 0 <= CAPOUT_MAX there (YCfn_cf.v fr_capout_ok_b, the cut's CAPOUT clause) *)
Lemma fr_capout_init : forall (W : world tfibsegs) (mem : word -> option byte),
  (forall a, Exists (in_zr a) GF_OBJ -> aview tfibsegs (w_H W) mem a = Some (gf_init a)) -> fr_capout_ok_b W mem.
Proof.
intros W mem HG. exists 0. split; [| rewrite CAPOUT_MAX_OUT_MAX; unfold OUT_MAX; lia].
intros k Hk. assert (Hi : 0 <= Z.of_nat k < 8) by lia.
pose proof (gf_words_zero _ Hi) as (_ & _ & Z3). pose proof (gf_words_in _ Hi) as (_ & _ & I3).
pose proof (HG _ I3) as E. rewrite Z3 in E. unfold aview in E. cbv beta in E.
change (mbyte tfibsegs (mrestrict (w_H W) mem) (0x5d90a0 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 0 8 k))).
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (0x5d90a0 + Z.of_nat k)) as [b|] eqn:Eb;
  rewrite ?Eb in E; cbn [option_map] in E; [|discriminate].
injection E as E. f_equal. apply bv_eq. rewrite E, Z_to_bv_unsigned.
assert (Hc : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%nat) by lia.
repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]). subst k. vm_compute. reflexivity.
Qed.
