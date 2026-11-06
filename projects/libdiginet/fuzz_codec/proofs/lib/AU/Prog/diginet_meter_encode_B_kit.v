(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths and module names changed; 510 of its 564 lines of code are new or changed and 527 lines of the source are left out. *)
(* The pieces of the image-B walk of diginet_meter_encode (diginet_codec.c:217-231; image B 0x85f4c, 161
   instructions) that its files share: the walk's arithmetic and memory lemmas, its kept invariant, the objects at
   the call of diginet_sysex_encode, the shapes of sysex_encode's result, the write-window tactic of its states, and
   the state ss_mtX at 0x86110 (with the join mtb_join to it), the block every path reaches before it releases its
   side-stack frame. The frame part follows image A's walk of diginet_scribble_encode, which has the same frame
   code.
   Atoms of the walk: 0..31 the registers at entry, 32 the shadow offset SB, 70 the realigned sp
   (sp1 = (sp - 128) & -32, s1), 75 the class-0 frame F = frame_addr lyc 0 pos, 87 its flag address, 88 the
   frame's shadow address SB + F / 8, 89 the personality's device byte, 600.. the result and the dead registers
   at 0x86110. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YC85 YCeo YI00 YF0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgWalkU CPgWalkKeptU CPgWalkFrameU CPgWalkCallU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_METER : Z := 0x85f4c.
Definition B_SYSEX : Z := 0x85174.
Definition B_MT_EXIT : Z := 0x86110.

(* ================================ arithmetic ================================ *)
(* `addi sp,sp,-128; andi sp,sp,-32` *)
Lemma mtb_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma mtb_count_cid_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c q] l IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.
(* enumerate the integer x from the bound Hl : lo <= x up to hi, closing each case by tac *)
Ltac mtb_zcases x hi tac :=
lazymatch goal with Hl : ?lo <= x |- _ =>
lazymatch eval vm_compute in (Z.leb lo hi) with
| true => let Heq := fresh "Heq" in let Hne := fresh "Hne" in
  destruct (Z.eq_dec x lo) as [Heq | Hne];
  [ subst x; tac
  | let lo' := eval vm_compute in (lo + 1) in assert (lo' <= x) by lia; clear Hl Hne; mtb_zcases x hi tac ]
| false => exfalso; lia
end end.
Lemma mtb_s32_small : forall c, 0 <= c < 2 ^ 31 -> s32 c = c.
Proof. intros c Hc. unfold s32. destruct (Z.ltb_spec c (2 ^ 31)); lia. Qed.
(* a 32-bit unsigned argument loaded with lw *)
Lemma mtb_U_u32 : forall E n c, ew E n = Z_to_bv 64 (s32 c) -> 0 <= c < 2 ^ 32 ->
U E (SOff n 0) = if c <? 2 ^ 31 then c else c + 18446744069414584320.
Proof.
intros E n c Hn Hc. rewrite U_SOff, Hn, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. unfold s32.
destruct (Z.ltb_spec c (2 ^ 31)); [apply Z.mod_small; lia|].
replace (c - 2 ^ 32) with ((c + 18446744069414584320) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* `bltu k, r` with r = a lw-loaded unsigned c and a small constant k: taken exactly when k < c *)
Lemma mtb_br_ltu_u32 : forall E n c k, ew E n = Z_to_bv 64 (s32 c) -> 0 <= c < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
branch_taken BC_LTU (sv_denot E (SLit k)) (sv_denot E (SOff n 0)) = (k <? c).
Proof.
intros E n c k Hn Hc Hk. rewrite branch_ltu_U, U_lit by lia. rewrite (mtb_U_u32 E n c Hn Hc).
destruct (Z.ltb_spec c (2 ^ 31)); [reflexivity|].
destruct (Z.ltb_spec k (c + 18446744069414584320)); destruct (Z.ltb_spec k c); first [reflexivity | lia].
Qed.
(* the payload's first byte: channel, with 0x20 when right is not 0 *)
Definition mch (ch r : Z) : Z := Z.lor ch (bit_or_0 (negb (r =? 0)) 0x20).
Lemma mtb_U_int : forall E n r, ew E n = Z_to_bv 64 r -> U E (SOff n 0) = r mod 2 ^ 64.
Proof.
intros E n r Hn. rewrite U_SOff, Hn, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* `snez a1,s7; slli a1,a1,5; or s4,a1,s4` on right (s7) and channel (s4) *)
Lemma mtb_U_ch : forall E c r, ew E 11 = Z_to_bv 64 c -> ew E 12 = Z_to_bv 64 r -> 0 <= c -> c <= 31 ->
- 2 ^ 31 <= r < 2 ^ 31 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 5)) (SOff 11 0)) = mch c r.
Proof.
intros E c r H11 H12 Hc0 Hc1 Hr. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom E 11 c H11) by lia.
rewrite (mtb_U_int E 12 r H12).
replace (zcanon 0 <? r mod 2 ^ 64) with (negb (r =? 0)).
2: { change (zcanon 0) with 0. destruct (Z.eqb_spec r 0) as [->|Hne]; [reflexivity|]. symmetry. apply Z.ltb_lt.
  destruct (Z.ltb_spec r 0).
  - rewrite <- (Z.mod_add r 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia. }
unfold mch, bit_or_0. destruct (negb (r =? 0)); mtb_zcases c 31 ltac:(vm_compute; reflexivity).
Qed.
Lemma mch_range : forall c r, 0 <= c < 32 -> 0 <= mch c r < 64.
Proof.
intros c r H. unfold mch, bit_or_0. destruct (negb (r =? 0)); destruct H as [H0 H1]; mtb_zcases c 31 ltac:(repeat split; vm_compute; congruence).
Qed.
(* `li a0,-1; sllw a0,a0,s6; not a0,a0` on segments s gives meter_mask; its two payload bytes *)
Definition sv_mask : sv := SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 13 0)) (SLit (-1)).
Lemma mtb_U_mask : forall E s, ew E 13 = Z_to_bv 64 s -> 0 <= s -> s <= 14 ->
U E sv_mask = meter_mask_spec s /\ U E (SAlu ALU_SRL sv_mask (SLit 7)) = Z.shiftr (meter_mask_spec s) 7 /\
U E (SAlu ALU_AND sv_mask (SLit 127)) = Z.land (meter_mask_spec s) 127.
Proof.
intros E s H13 Hs0 Hs1. unfold sv_mask. rewrite !U_SAlu, !U_SLit, U_of_S, S_SAluw, !U_SLit, (U_atom E 13 s H13) by lia.
cbn [zalu_raw]. mtb_zcases s 14 ltac:(vm_compute; repeat (split || reflexivity)).
Qed.
Lemma mtb_mask_bytes : forall s, 0 <= s -> s <= 14 ->
0 <= Z.shiftr (meter_mask_spec s) 7 < 128 /\ 0 <= Z.land (meter_mask_spec s) 127 < 128.
Proof. intros s H0 H1. mtb_zcases s 14 ltac:(repeat split; vm_compute; congruence). Qed.
(* a value v in a register expression e as a 64-bit literal *)
Lemma mtb_denot_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite denot_lit_U. f_equal. exact H. Qed.
(* the key the code stores: `lui a1,0x40; or a1,s4,a1` on the payload's first byte v *)
Lemma mtb_key_val : forall v, 0 <= v < 64 -> zcanon (zalu_raw 63 64 ALU_OR v (zcanon 262144)) = KEY 4 (u8 v).
Proof. intros v [Hv0 Hv1]. mtb_zcases v 63 ltac:(vm_compute; reflexivity). Qed.
Lemma mtb_key_denot : forall E e v, U E e = v -> 0 <= v < 64 ->
sv_denot E (SAlu ALU_OR e (SLit 262144)) = Z_to_bv 64 (KEY 4 (u8 v)).
Proof.
intros E e v Hv Hr. apply mtb_denot_of_U. rewrite U_SAlu, U_SLit, Hv. exact (mtb_key_val v Hr).
Qed.
Lemma mtb_key_range : forall v, 0 <= v < 64 -> 0 <= KEY 4 (u8 v) < 2 ^ 32.
Proof.
intros v [Hv0 Hv1]. unfold KEY, u8. rewrite (Z.mod_small v 256) by lia. mtb_zcases v 63 ltac:(vm_compute; split; congruence).
Qed.

(* ================================ meter_spec on each path ================================ *)
Lemma mtb_spec_range_ch : forall d ch r s, 32 <= ch -> meter_spec (Some d) ch r s = (E_RANGE, None).
Proof.
intros d ch r s H. cbv beta iota zeta delta [meter_spec].
replace (0x20 <=? ch) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma mtb_spec_range_seg : forall d ch r s, 14 < s -> meter_spec (Some d) ch r s = (E_RANGE, None).
Proof.
intros d ch r s H. cbv beta iota zeta delta [meter_spec].
replace (14 <? s) with true by (symmetry; apply Z.ltb_lt; lia). rewrite orb_true_r. reflexivity.
Qed.
(* the in-range case: sysex_encode of the three payload bytes, then the key *)
Lemma mtb_spec_sysex : forall d c r s, 0 <= c < 32 -> 0 <= s <= 14 ->
meter_spec (Some d) c r s =
with_key (sysex_spec (d_dev d) 16 [u8 (mch c r); u8 (Z.shiftr (meter_mask_spec s) 7); u8 (Z.land (meter_mask_spec s) 0x7f)])
  (KEY 4 (u8 (mch c r))).
Proof.
intros d c r s H1 H2. cbv beta iota zeta delta [meter_spec].
replace (0x20 <=? c) with false by (symmetry; apply Z.leb_gt; lia).
replace (14 <? s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* ================================ the walk's write windows ================================ *)
(* The windows of the walk's states: the save area (atom 2, sp), the spill 24(s1) (atom 70, sp1), the frame
   (atom 75) and its shadow (atom 88), both the walk's own frame (0, pos), the head of the journal's own list. *)
(* close `q = frame_addr ly 0 pos` or `SB + q / 8 = shadow_addr (frame_addr ly 0 pos)` for the walk's F, the layout
   ly possibly a later one with the same frame addresses (Efa) *)
Ltac mtb_fa :=
try (lazymatch goal with Hf : forall c p, frame_addr _ c p = frame_addr _ c p |- _ => rewrite ?Hf end);
try (unfold shadow_addr, SHADOW_OFF); rewrite ?unsigned_lit_small by lia; first [reflexivity | lia].
Ltac mtb_awr AG spv sp1v pos :=
idtac; cw_awrA;
lazymatch goal with |- YCbq.awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (YCbq.awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply YCbq.awr_ok_nil
| apply YCbq.awr_ok_cons_ro; [azlit_tac|]
| lazymatch goal with |- YCbq.awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (YCbq.awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
    [reflexivity | evalE AG | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end
| lazymatch goal with |- YCbq.awr_ok _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (YCbq.awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (sp1v - sp0));
    [reflexivity | evalE AG | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end
| lazymatch goal with |- YCbq.awr_ok _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _ :: _) _ _ _ _ _ ?lyv _ =>
    eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ lyv _ 0 pos);
    [reflexivity | evalE AG; mtb_fa | left; reflexivity | apply Z.leb_le; vm_compute; reflexivity
    | apply Z.leb_le; vm_compute; reflexivity |] end
| lazymatch goal with |- YCbq.awr_ok _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _ :: _) _ _ _ _ _ ?lyv _ =>
    eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ lyv _ 0 pos);
    [reflexivity | evalE AG; mtb_fa | left; reflexivity
    | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |] end ];
lazymatch goal with |- YCbq.awr_ok _ (?r :: _) _ _ _ _ _ _ _ => fail 1 "mtb_awr: no rule for" r | _ => idtac end
end.
(* the engine's shadow table: the given entries SH0 (closed by tac0) and the app-memory entries of the state's
   writable windows *)
Ltac mtb_shok SH0 tac0 :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch goal with HS : st_ok ?segs ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
let SH := eval vm_compute in (SH0 ++ app_entries (ss_facts ss) (ss_mem ss)) in
let SHOK := fresh "SHOK" in
shok_assert SHOK segs CW_Bx SH Ex (mrestrict (w_H Wx) (ms_mem msx)) tac0 end.
Ltac mtb_shok0 :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch goal with HS : st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) |- _ =>
let SH := fresh "SHOK" in assert (SH : sh_ok tfibsegs CW_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by constructor end.
(* a rebase of the environment that carries env_agree 32 E0 E along *)
Ltac mtb_rebase HS AG HAE :=
let HEv := fresh "HEv" in
rebaseE HS AG HEv;
lazymatch type of HAE with env_agree 32 ?E0 _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let H2 := fresh "HAE" in
assert (H2 : env_agree 32 E0 Ev) by (rewrite HEv; env_agree_chain HAE);
clear HAE; rename H2 into HAE end end;
clear HEv.

(* ================================ the exit block 0x86110 ================================
   Live: sp = s1 = sp1 (70), gp, tp, s0 = sp (2), s2 = s8 = F (75), s9 = SB + F / 8 (88), and a0 = the result,
   the first of the fresh atoms 600.. (the other registers are dead and take the next ones); memory: the frame's
   shadow (88), the frame (75, the flag address at F + 56), the save area (2). *)
(* s11 (x27) is a register the function never writes: it stays at its entry value, so it is not one of these *)
Definition mtb_X_deads : list nat := [10; 1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 26; 28; 29; 30; 31]%nat.
Definition mtb_X_deads_bv : list (bv 5) := [10; 1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 26; 28; 29; 30; 31]%bv.
Definition MTB_XN : nat := 600.
Definition mtb_saves : list YP09.chunk :=
[ YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
  YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Definition mtb_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 mtb_saves.
Definition mtb_frame : YP09.region := YP09.mkRegion (Some 75%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 87 0))].
Definition mtb_fsh : YP09.region := YP09.mkRegion (Some 88%nat) 0 8 0 8 [].
Definition mtb_X_atoms : list (nat * afact) :=
[ (88%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (87%nat, HPTR 0); (75%nat, HPTR 6);
  (70%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ].
Definition mtb_X_0 : sstate :=
mkSS B_MT_EXIT
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 70 0; SOff 89 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
 SOff 75 0; SOff 88 0; SOff 32 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[ mtb_fsh; mtb_frame; mtb_stack ] None (mkFacts mtb_X_atoms [] []).
Definition ss_mtX : sstate := Eval vm_compute in ss_havoc_regs mtb_X_0 MTB_XN mtb_X_deads.
(* A state at 0x86110 joined to ss_mtX: the dead registers (a0 first) moved to the fresh atoms 600.., the regions
   cut to the frame, its shadow and the save area, the facts cut to mtb_X_atoms. *)
Ltac mtb_join HS :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let vals := eval cbv [map mtb_X_deads_bv] in (map (fun r => getr (ms_regs msv) r) mtb_X_deads_bv) in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_agree tfibsegs 600 Ev (havoc Ev 600 vals) ssv msv HS
    (env_agree_havoc_ge 600 600 Ev Ev vals (le_n _) (env_agree_refl 600 Ev)) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS;
  let rl := eval cbv [mtb_X_deads_bv] in mtb_X_deads_bv in
  set_regs_rec HS 600%nat vals 0%nat rl
end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_submem tfibsegs Ev ssv msv [mtb_fsh; mtb_frame; mtb_stack] HS
    ltac:(cbv [mtb_frame mtb_fsh mtb_stack mtb_saves]; cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS
end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_facts_incl3 tfibsegs Ev _ msv mtb_X_atoms [] [] HS
    ltac:(cbv [mtb_X_atoms]; cbn [ss_facts f_atoms]; incl_lit_tac)
    ltac:(let x := fresh "x" in intros x []) ltac:(let x := fresh "x" in intros x [])) as HS3;
  clear HS; rename HS3 into HS
end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  replace ssv with ss_mtX in HS by (vm_compute; reflexivity) end.

(* a byte the caller's journal lets it write stays so with one more own frame *)
Lemma mtb_awr_byte_cons : forall STK sp0 FP bl0 blc ly own c a,
YCbq.awr_byte STK sp0 FP bl0 blc ly own a -> YCbq.awr_byte STK sp0 FP bl0 blc ly (c :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own c a [H|[H|[H|(cid & ps & Hin & Hr)]]].
- left. exact H.
- right; left. exact H.
- right; right; left. exact H.
- right; right; right. exists cid, ps. split; [right; exact Hin | exact Hr].
Qed.

(* sysex_encode either fails without a command or succeeds with key 0 and at most 24 bytes *)
Lemma mtb_sysex_shape : forall dev fn pl,
(exists rc, sysex_spec dev fn pl = (rc, None) /\ -11 <= rc <= -1) \/
(exists bs dp, sysex_spec dev fn pl = (0, Some (bs, 0, dp)) /\ (length bs <= 24)%nat).
Proof.
intros dev fn pl. unfold sysex_spec.
destruct (0x7f <? dev); [left; eexists; split; [reflexivity | unfold E_ARG; lia]|].
destruct (fn =? 0x70); [left; eexists; split; [reflexivity | unfold E_REFUSED; lia]|].
destruct (0x7f <? fn); [left; eexists; split; [reflexivity | unfold E_RANGE; lia]|].
destruct (24 <? Z.of_nat (length pl) + 5) eqn:Hl; [left; eexists; split; [reflexivity | unfold E_SPACE; lia]|].
destruct (existsb (fun x => Z.testbit x 7) pl); [left; eexists; split; [reflexivity | unfold E_RANGE; lia]|].
right. do 2 eexists. split; [reflexivity|]. apply Z.ltb_ge in Hl.
rewrite app_length, app_length. cbn [length]. lia.
Qed.
Lemma mtb_with_key_none : forall rc k, with_key (rc, None) k = (rc, None).
Proof. intros [|q|q] k; reflexivity. Qed.
(* the command bytes of a success with the key replaced: the first 28 bytes, then the key's four *)
Lemma mtb_cmd_key : forall before bs dp k0 k, length before = 32%nat -> (length bs <= 24)%nat ->
cmd_outZ before (Some (bs, k, dp)) = firstn 28 (cmd_outZ before (Some (bs, k0, dp))) ++ le4Z k.
Proof.
intros before bs dp k0 k Hb Hs. unfold cmd_outZ.
set (P := map u8 bs ++ skipn (length bs) (firstn 24 before) ++ [u8 (Z.of_nat (length bs)); u8 dp] ++ firstn 2 (skipn 26 before)).
assert (LP : length P = 28%nat)
  by (unfold P; rewrite !app_length, map_length, skipn_length, !firstn_length, skipn_length; cbn [length]; lia).
assert (E : forall K, map u8 bs ++ skipn (length bs) (firstn 24 before) ++ [u8 (Z.of_nat (length bs)); u8 dp] ++
  firstn 2 (skipn 26 before) ++ le4Z K = P ++ le4Z K)
  by (intros K; unfold P; rewrite <- !app_assoc; reflexivity).
rewrite !E. rewrite firstn_app, LP, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.
Lemma mtb_cmd_len : forall before bs k dp, length before = 32%nat -> (length bs <= 24)%nat ->
length (cmd_outZ before (Some (bs, k, dp))) = 32%nat.
Proof.
intros before bs k dp Hb Hs. unfold cmd_outZ.
rewrite !app_length, map_length, skipn_length, !firstn_length, skipn_length. unfold le4Z. cbn [length]. lia.
Qed.
(* four bytes stored as a 4-byte value are its le4Z bytes *)
Lemma mtb_le4_garr8 : forall (m : word -> option byte) a v, 0 <= v < 2 ^ 32 ->
val_mem tfibsegs m a 4 v -> garr8 tfibsegs m a (le4Z v).
Proof.
intros m a v Hv V j Hj. cbn [length le4Z] in Hj.
assert (E : forall i, (i < 4)%nat -> val_mem tfibsegs m (a + Z.of_nat i) 1 ((v / 2 ^ (8 * Z.of_nat i)) mod 256)).
{ intros i Hi jj Hjj. assert (jj = 0%nat) by lia. subst jj. rewrite Z.add_0_r. cbn [Z.of_nat].
  specialize (V i Hi). rewrite V. f_equal. f_equal. unfold YO0f.le_byte.
  rewrite ?Z.shiftr_div_pow2 by lia. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia).
  cbn [Z.of_nat]. rewrite ?Z.mul_0_r, ?Z.pow_0_r, ?Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_mod by lia. reflexivity. }
destruct j as [|[|[|[|j]]]]; [| | | | lia]; cbn [nth le4Z].
- pose proof (E 0%nat ltac:(lia)) as E0. cbn [Z.of_nat] in E0. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r in E0.
  split; [exact E0 | apply Z.mod_pos_bound; lia].
- split; [exact (E 1%nat ltac:(lia)) | apply Z.mod_pos_bound; lia].
- split; [exact (E 2%nat ltac:(lia)) | apply Z.mod_pos_bound; lia].
- split; [exact (E 3%nat ltac:(lia)) | apply Z.mod_pos_bound; lia].
Qed.
Lemma mtb_garr8_app : forall (m : word -> option byte) a l1 l2,
garr8 tfibsegs m a l1 -> garr8 tfibsegs m (a + Z.of_nat (length l1)) l2 -> garr8 tfibsegs m a (l1 ++ l2).
Proof.
intros m a l1 l2 G1 G2 j Hj. rewrite app_length in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [H|H].
- rewrite app_nth1 by exact H. exact (G1 j H).
- rewrite app_nth2 by exact H. destruct (G2 (j - length l1)%nat ltac:(lia)) as (V & Hb). split; [|exact Hb].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact V.
Qed.
Lemma mtb_garr8_firstn : forall (m : word -> option byte) a l n, garr8 tfibsegs m a l -> garr8 tfibsegs m a (firstn n l).
Proof.
intros m a l n G j Hj. rewrite firstn_length in Hj. rewrite nth_firstn.
replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply G. lia.
Qed.

Lemma mtb_awr_byte_mono : forall STK sp0 FP bl0 blc blc' ly ly' own own' a,
YCbq.awr_byte STK sp0 FP bl0 blc ly own a ->
(forall b m, In (b, m) blc -> In (b, m) blc') -> incl own own' -> (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
YCbq.awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a [H|[(H1 & bb & mm & Hin & Hr)|[(bb & mm & Hin & Hn & Hr)|(cid & ps & Hin & Hr)]]] Hb Hown Efa.
- left. exact H.
- right; left. split; [exact H1|]. exists bb, mm. split; [exact (Hb bb mm Hin) | exact Hr].
- right; right; left. exists bb, mm. split; [exact (Hb bb mm Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, ps. split; [exact (Hown _ Hin)|]. rewrite !Efa. exact Hr.
Qed.

(* bytes off every write window of a run keep their values *)
Lemma mtb_garr8_run : forall (Ev : env) rs H (m1 m2 : word -> option byte) (Zn : Z -> Prop) q l,
frame_of Ev rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange Ev rs a -> Zn a) ->
(forall a, q <= a < q + Z.of_nat (length l) -> ~ Zn a) -> 0 <= q -> q + Z.of_nat (length l) <= 2 ^ 64 ->
garr8 tfibsegs (mrestrict H m1) q l -> garr8 tfibsegs (mrestrict H m2) q l.
Proof.
intros Ev rs H m1 m2 Zn q l HFr HW Hn Hq0 Hq1 G j Hj. destruct (G j Hj) as (V & Hb). split; [|exact Hb].
apply (cw_val_mem_kept H H m1 m2 _ 1 _); [|exact V].
intros x Hx. change (Z.of_nat 1) with 1 in Hx.
unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 x)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hw. exact (Hn x ltac:(lia) (HW x Hw)).
Qed.
(* the payload pl at F + 32: its three bytes *)
Lemma mtb_pl_garr8 : forall H (m : word -> option byte) F b0 b1 b2,
0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
val_mem tfibsegs (mrestrict H m) (F + 32) 1 b0 -> val_mem tfibsegs (mrestrict H m) (F + 33) 1 b1 ->
val_mem tfibsegs (mrestrict H m) (F + 34) 1 b2 ->
garr8 tfibsegs (mrestrict H m) (F + 32) [u8 b0; u8 b1; u8 b2].
Proof.
intros H m F b0 b1 b2 R0 R1 R2 V0 V1 V2 j Hj. cbn [length] in Hj. unfold u8.
destruct j as [|[|[|j]]]; [| | | lia]; cbn [nth].
- rewrite Z.mod_small by lia. rewrite Z.add_0_r. split; [exact V0 | lia].
- rewrite Z.mod_small by lia. replace (F + 32 + Z.of_nat 1) with (F + 33) by lia. split; [exact V1 | lia].
- rewrite Z.mod_small by lia. replace (F + 32 + Z.of_nat 2) with (F + 34) by lia. split; [exact V2 | lia].
Qed.

(* ================================ the frame's zone ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* A frame position the call state does not hold is the runtime's own there: its bytes and its shadow
   (YF0v own_free_frame / own_free_frame_shadow), with the position's bounds from the state that holds it. *)
Lemma mtb_fz_owned : forall lyc Sc (W : world tfibsegs) memc mdc S2 (W2 : world tfibsegs) m2 md2 pos a,
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B lyc S2 W2 m2 md2 -> In (0, pos) (frames S2) -> ~ In (0, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (0, pos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8)) ->
aowned B lyc Sc a.
Proof.
intros lyc Sc W memc mdc S2 W2 m2 md2 pos a HAR HAR2 Hin Hnin Ha.
destruct (frame_facts B lyc S2 _ 0 pos (proj1 HAR2) Hin) as (Hc & Hp & _).
unfold frame_rng, in_zr in Ha. cbn [fst snd] in Ha.
destruct Ha as [Ha | Ha].
- exact (own_free_frame B lyc Sc _ 0 pos a (proj1 HAR) Hc Hp Hnin Ha).
- exact (own_free_frame_shadow B lyc Sc _ 0 pos a (proj1 HAR) Hc Hp Hnin Ha).
Qed.
(* The shadow window of every byte of a range in heap blocks or live frames of a state is readable: each 8-byte
   window of the range's hull is the window of one of its bytes. *)
Lemma mtb_hull_tdst : forall ly S (W : world tfibsegs) mem md q n,
AR tfibsegs B ly S W mem md -> tdst_ok B ly S q n -> 0 < n -> 0 <= q ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) q n.
Proof.
intros ly S W mem md q n HAR Hd Hn Hq s Hs.
assert (EL : forall y, 0 <= y -> shadow_addr y / 8 = 268431360 + y / 64).
{ intros y Hy. unfold shadow_addr, SHADOW_OFF.
  replace (2147450880 + y / 8) with (y / 8 + 268431360 * 8) by lia. rewrite Z.div_add by lia.
  rewrite Z.div_div by lia. change (8 * 8) with 64. lia. }
rewrite !EL in Hs by lia.
set (L := s / 8 - 268431360).
assert (HL1 : q / 64 <= L).
{ assert (268431360 + q / 64 <= s / 8) by (apply Z.div_le_lower_bound; lia). unfold L. lia. }
assert (HL2 : L <= (q + n - 1) / 64).
{ assert (s / 8 < 268431360 + (q + n - 1) / 64 + 1) by (apply Z.div_lt_upper_bound; lia). unfold L. lia. }
set (y := Z.max q (64 * L)).
assert (Hy : q <= y < q + n).
{ unfold y. split; [lia|]. pose proof (Z.mul_div_le (q + n - 1) 64 ltac:(lia)). lia. }
assert (Hy64 : y / 64 = L).
{ unfold y. destruct (Z.le_ge_cases q (64 * L)) as [H1 | H1].
  - rewrite Z.max_r by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  - rewrite Z.max_l by lia. assert (q / 64 >= L) by (apply Z.le_ge, Z.div_le_lower_bound; lia). lia. }
assert (HV : shadow_hull_vis (aview tfibsegs (w_H W) mem) y 1).
{ destruct (Hd y Hy) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)].
  - apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W mem md b m y 1 HAR Hin); lia.
  - unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    apply (shadow_hull_vis_of_frame tfibsegs B LAWS ly S W mem md cid pos y 1 HAR Hin); lia. }
apply HV. rewrite Z.add_simpl_r, !EL by lia. rewrite Hy64. unfold L in *.
pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)). lia.
Qed.
(* The usable marks of a range in heap blocks or frames of the call state, kept at a later state that holds the
   same blocks and keeps the frames' shadow bytes. *)
Lemma mtb_ra_tdst : forall lyc Sc (W : world tfibsegs) memc mdc ly1 S1 (W1 : world tfibsegs) m1 md1 q n,
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B ly1 S1 W1 m1 md1 -> tdst_ok B lyc Sc q n ->
(forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly1 S1)) ->
(forall cid pos a, In (cid, pos) (frames Sc) -> in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
  aview tfibsegs (w_H W1) m1 a = aview tfibsegs (w_H W) memc a) ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF q n ->
range_addressable (aview tfibsegs (w_H W1) m1) SHADOW_OFF q n.
Proof.
intros lyc Sc W memc mdc ly1 S1 W1 m1 md1 q n HAR HAR1 Hd Hbl Hfs Hra x Hx.
destruct (Hd x Hx) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- exact (range_addressable_of_block tfibsegs B LAWS ly1 S1 W1 m1 md1 b m x 1 HAR1 (Hbl b m Hin) ltac:(lia) ltac:(lia) x ltac:(lia)).
- destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. apply (Hfs cid pos); [exact Hin|].
  destruct (frame_al64 tfibsegs B lyc Sc W memc mdc cid pos HAR Hin) as (Ha64 & Hb64 & _).
  destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H4096 & _ & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
  set (F := frame_addr lyc cid pos) in *. set (bs := fs_frame_bytes cid) in *.
  apply Z.mod_divide in Ha64 as [qa Hqa]; [|lia]. apply Z.mod_divide in Hb64 as [qb Hqb]; [|lia].
  assert (EF : F / 8 = 8 * qa) by (rewrite Hqa; replace (qa * 64) with ((8 * qa) * 8) by lia; apply Z.div_mul; lia).
  assert (Eb : bs / 8 = 8 * qb) by (rewrite Hqb; replace (qb * 64) with ((8 * qb) * 8) by lia; apply Z.div_mul; lia).
  rewrite EF, Eb. split.
  + assert (8 * qa <= x / 8) by (apply Z.div_le_lower_bound; lia). lia.
  + assert (x / 8 < 8 * qa + 8 * qb) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
(* tcj_kept is monotone in the write set *)
Lemma mtb_tcj_mono : forall T lyc Sc (W : world tfibsegs) m (W2 : world tfibsegs) m2 sp (E E' : Z -> Prop),
(forall a, E a -> E' a) -> tcj_kept tfibsegs B T lyc Sc W m W2 m2 sp E -> tcj_kept tfibsegs B T lyc Sc W m W2 m2 sp E'.
Proof.
intros T lyc Sc W m W2 m2 sp E E' HEE (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hw HE; apply K1; [exact Ha | exact Hw | intros X; exact (HE (HEE a X))]|].
split; [intros bb mm i Hin Hi HE; apply (K2 bb mm i Hin Hi); intros X; exact (HE (HEE _ X))|].
split; [exact K3|].
split; [intros cid pos a Hin Hr HE; apply (K4 cid pos a Hin Hr); intros X; exact (HE (HEE a X))|].
split; [exact K5 | exact K6].
Qed.
(* a byte of a heap block or of a live frame of a state is not the runtime's own there *)
Lemma mtb_tdst_not_owned : forall ly S (W : world tfibsegs) mem md q n a,
AR tfibsegs B ly S W mem md -> tdst_ok B ly S q n -> q <= a < q + n -> ~ aowned B ly S a.
Proof.
intros ly S W mem md q n a HAR Hd Ha.
destruct (Hd a Ha) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS ly S W mem md bb m HAR Hin) as (_ & _ & _ & _ & Hbo & _).
  replace a with (bb + (a - bb)) by lia. exact (proj2 (Hbo (bb + (a - bb)) ltac:(lia))).
- unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  intros (_ & Hnc). apply Hnc. right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* the window or the walk's own frame and its shadow *)
Definition mtb_wz (sp : Z) (lyc : alayout) (pos a : Z) : Prop :=
(sp - TB_meter <= a < sp) \/ in_zr a (frame_rng lyc (0, pos)) \/
in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8).
(* The walk's kept invariant through a run whose writes lie in the window or in the walk's own frame. *)
Lemma mtb_kt_run : YCbq.frame_flag_lawP tfibsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k ly2 S2 (W2 : world tfibsegs) m2 md2 k2 pos sp
(E X : Z -> Prop) (W1 : world tfibsegs) m1 m3,
YCbq.ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YCbq.ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) ly2 S2 W2 m2 md2 k2 ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> alloc_ceiling <= sp - TB_meter ->
tcj_kept tfibsegs B TB_meter lyc Sc W memc W1 m1 sp E ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H W1) m3 a = aview tfibsegs (w_H W1) m1 a) ->
(forall a, X a -> mtb_wz sp lyc pos a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m3 a) ->
tcj_kept tfibsegs B TB_meter lyc Sc W memc W1 m3 sp E.
Proof.
intros FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 m2 md2 k2 pos sp E X W1 m1 m3
HJ0 HJ2 HP Hce KT HX HXc Hpr.
apply (cw_kept_step B LAWS TB_meter lyc Sc W memc mdc W1 m1 m3 sp E X Hce (proj1 HJ0) KT HX); [|exact Hpr].
intros a Hx. destruct (HXc a Hx) as [Hw | Hf]; [left; exact Hw|].
right; right. apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 m2 md2 k2 0 pos a HJ0 HJ2 HP).
destruct Hf as [Hf | Hf]; [left; exact Hf | right; left; exact Hf].
Qed.
(* The values of the bytes that are neither the runtime's own in the call state nor in the window. *)
Definition mtb_ka (lyc : alayout) (Sc : astate) (sp : Z) (H : word -> bool) (m m0 : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (aowned B lyc Sc a \/ sp - TB_meter <= a < sp) -> aview tfibsegs H m a = aview tfibsegs H m0 a.
Lemma mtb_ka_run : forall lyc Sc (W : world tfibsegs) memc mdc S2 (W2 : world tfibsegs) m2 md2 pos sp (X : Z -> Prop) H m1 m3 m0,
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B lyc S2 W2 m2 md2 -> In (0, pos) (frames S2) -> ~ In (0, pos) (frames Sc) ->
mtb_ka lyc Sc sp H m1 m0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs H m3 a = aview tfibsegs H m1 a) ->
(forall a, X a -> mtb_wz sp lyc pos a) ->
mtb_ka lyc Sc sp H m3 m0.
Proof.
intros lyc Sc W memc mdc S2 W2 m2 md2 pos sp X H m1 m3 m0 HAR HAR2 Hin Hnin KA HX HXc a Ha Hn.
rewrite (HX a Ha); [exact (KA a Ha Hn)|].
intros Hx. apply Hn. destruct (HXc a Hx) as [Hw | Hf]; [right; exact Hw|].
left. exact (mtb_fz_owned lyc Sc W memc mdc S2 W2 m2 md2 pos a HAR HAR2 Hin Hnin Hf).
Qed.
(* the same through a run that writes only the window *)
Lemma mtb_ka_run0 : forall lyc Sc sp (X : Z -> Prop) H m1 m3 m0,
mtb_ka lyc Sc sp H m1 m0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs H m3 a = aview tfibsegs H m1 a) ->
(forall a, X a -> sp - TB_meter <= a < sp) ->
mtb_ka lyc Sc sp H m3 m0.
Proof.
intros lyc Sc sp X H m1 m3 m0 KA HX HXc a Ha Hn.
rewrite (HX a Ha); [exact (KA a Ha Hn)|]. intros Hx. apply Hn. right. exact (HXc a Hx).
Qed.
(* the bytes of an object in blocks or frames of the call state, kept by a walk that writes no such byte *)
Lemma mtb_garr8_kept : forall T lyc Sc (W : world tfibsegs) memc (W1 : world tfibsegs) m1 sp q l,
tdst_ok B lyc Sc q (Z.of_nat (length l)) ->
tcj_kept tfibsegs B T lyc Sc W memc W1 m1 sp (fun _ => False) ->
garr8 tfibsegs (mrestrict (w_H W) memc) q l -> garr8 tfibsegs (mrestrict (w_H W1) m1) q l.
Proof.
intros T lyc Sc W memc W1 m1 sp q l Hd (_ & K2 & _ & K4 & _) Hg j Hj.
destruct (Hg j Hj) as (Hv & Hb). split; [|exact Hb].
apply (cw_val_mem_kept (w_H W) (w_H W1) memc m1 _ 1 _); [|exact Hv].
intros x Hx. change (Z.of_nat 1) with 1 in Hx.
destruct (Hd x ltac:(lia)) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- replace x with (bb + (x - bb)) by lia. exact (K2 bb m (x - bb) Hin ltac:(lia) (fun H => H)).
- exact (K4 cid pos x Hin (or_introl Hr) (fun H => H)).
Qed.
(* an object in blocks or frames of the call state lies below the allocator ceiling *)
Lemma mtb_tdst_below : forall lyc Sc (W : world tfibsegs) memc mdc q n,
AR tfibsegs B lyc Sc W memc mdc -> tdst_ok B lyc Sc q n -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof.
intros lyc Sc W memc mdc q n HAR Hd Hn.
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc q n q HAR Hd ltac:(lia)) as (H1 & _).
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc q n (q + n - 1) HAR Hd ltac:(lia)) as (H2 & _).
lia.
Qed.
(* a range of fresh bytes is apart from an object in blocks or frames of the call state *)
Lemma mtb_fresh_disj2 : forall lyc Sc q n x m, tdst_ok B lyc Sc q n ->
(forall a, x <= a < x + m -> cw_fresh B lyc Sc a) -> 0 < n -> 0 < m -> x + m <= q \/ q + n <= x.
Proof.
intros lyc Sc q n x m Hd Hf Hn Hm.
destruct (Z_le_gt_dec (x + m) q) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (q + n) x) as [H2|H2]; [right; exact H2|].
exfalso. set (a := Z.max q x).
destruct (Hf a ltac:(unfold a; lia)) as (_ & _ & Hb & Hfr).
destruct (Hd a ltac:(unfold a; lia)) as [(bb & mm & Hin & Hr) | (cid & ps & Hin & Hr)].
- exact (Hb bb mm (a - bb) Hin ltac:(lia) ltac:(lia)).
- exact (proj1 (Hfr cid ps Hin) Hr).
Qed.
(* an object of the call state is one of the state after the walk's frame request *)
Lemma mtb_tdst_req : forall lyc Sc S2 c q n, tdst_ok B lyc Sc q n ->
ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = c :: frames Sc -> tdst_ok B lyc S2 q n.
Proof.
intros lyc Sc S2 c q n Hd Eab Hfr a Ha.
destruct (Hd a Ha) as [(bb & mm & Hin & Hr) | (cid & ps & Hin & Hr)].
- left. exists bb, mm. rewrite Eab. split; [exact Hin | exact Hr].
- right. exists cid, ps. rewrite Hfr. split; [right; exact Hin | exact Hr].
Qed.
(* a byte of a heap block or of a live frame of a state is present *)
Lemma mtb_tdst_present : forall ly S (W : world tfibsegs) mem md q n a,
AR tfibsegs B ly S W mem md -> tdst_ok B ly S q n -> q <= a < q + n -> apresent (w_H W) mem a.
Proof.
intros ly S W mem md q n a HAR Hd Ha.
destruct (Hd a Ha) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS ly S W mem md bb m HAR Hin) as (_ & _ & _ & _ & Hbo & _).
  replace a with (bb + (a - bb)) by lia. exact (proj1 (Hbo (bb + (a - bb)) ltac:(lia))).
- destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hfb & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Hfb a ltac:(lia))).
Qed.
(* The caller's command at the call of sysex: the request's frame in front, the walk's memory since the entry *)
Lemma mtb_cdst_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k S2 pos m md sp sp1 out,
YCbq.ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YCbq.ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W m md k ->
ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = (0, pos) :: frames Sc ->
tcj_kept tfibsegs B TB_meter lyc Sc W memc W m sp (fun _ => False) ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp TB_meter out 32 ->
alloc_ceiling <= sp - TB_meter -> sp - 144 <= sp1 <= sp ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc S2 ((0, pos) :: own) W m sp1 TB_sysex out 32.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 pos m md sp sp1 out HJ0 HJ Eab Hfr KT
(Hq0 & Hq63 & Htd & Htw & Hra & Hhull & Ham & Hwin) Hce Hsp1.
pose proof KT as (_ & _ & _ & K4 & _).
pose proof (mtb_tdst_req lyc Sc S2 (0, pos) out 32 Htd Eab Hfr) as Htd2.
pose proof (proj1 HJ0) as HAR. pose proof (proj1 HJ) as HAR2.
unfold TB_meter, TB_sysex, ESTACK in *.
split; [lia|]. split; [lia|]. split; [exact Htd2|].
split.
{ intros a Ha. destruct (Htw a Ha) as (Haw & _ & _ & _).
  pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 a HAR Htd Ha) as (Hb1 & _).
  split; [rewrite Eab; apply mtb_awr_byte_cons; exact Haw|].
  split; [exact (mtb_tdst_present lyc S2 W m md out 32 a HAR2 Htd2 Ha)|].
  split; [exact (mtb_tdst_not_owned lyc S2 W m md out 32 a HAR2 Htd2 Ha)|].
  unfold ESTACK. lia. }
split.
{ apply (mtb_ra_tdst lyc Sc W memc mdc lyc S2 W m md out 32 HAR HAR2 Htd).
  - intros bb mm Hin. rewrite Eab. exact Hin.
  - intros cid ps a Hin Hr. exact (K4 cid ps a Hin (or_intror Hr) (fun H => H)).
  - exact Hra. }
split; [intros _; apply (mtb_hull_tdst lyc S2 W m md out 32 HAR2 Htd2); lia|].
split; [exact Ham|].
left. pose proof (mtb_tdst_below lyc Sc W memc mdc out 32 HAR Htd ltac:(lia)). lia.
Qed.
(* an object of a state is one of a later state with more blocks and frames at the same addresses *)
Lemma mtb_tdst_mono : forall lyc Sc ly4 S4 q n, tdst_ok B lyc Sc q n ->
(forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly4 S4)) ->
(forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S4)) ->
(forall c p, frame_addr ly4 c p = frame_addr lyc c p) -> tdst_ok B ly4 S4 q n.
Proof.
intros lyc Sc ly4 S4 q n Hd Hb Hf Efa a Ha.
destruct (Hd a Ha) as [(bb & mm & Hin & Hr) | (cid & ps & Hin & Hr)].
- left. exists bb, mm. split; [exact (Hb bb mm Hin) | exact Hr].
- right. exists cid, ps. split; [exact (Hf cid ps Hin)|]. unfold frame_rng in *. rewrite Efa. exact Hr.
Qed.
End d.
End b.
