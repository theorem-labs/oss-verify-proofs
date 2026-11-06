(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths and module names changed; 468 of its 525 lines of code are new or changed and 524 lines of the source are left out. *)
(* The pieces of the image-B walk of diginet_counter_encode (diginet_codec.c:371-386; image B 0x86ee4, 191
   instructions) that its files share: the payload and the result in terms of diginet_sysex_encode's, the walk's
   arithmetic and memory lemmas, its kept invariant, the objects at the call of sysex_encode, the write-window
   tactic of its states, and the state ss_ctrX at 0x870fc (with the join cbe_join to it), the block every path
   reaches before it releases its side-stack frame.
   Atoms of the walk: 0..31 the registers at entry, 32 the shadow offset SB, 70 the realigned sp
   (sp1 = (sp - 128) & -32, s1), 75 the class-0 frame F = frame_addr lyc 0 pos, 87 its flag address, 88 the
   frame's shadow address SB + F / 8, 89 and 90 the personality's device and counter address, 91..98 seg[0..8),
   600.. the result and the dead registers at 0x870fc. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YCbqU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_CTR : Z := 0x86ee4.
Definition B_SYSEX : Z := 0x85174.
Definition B_CTR_EXIT : Z := 0x870fc.
Lemma TB_counter_val : TB_counter = 4304.
Proof. reflexivity. Qed.
Lemma TB_sysex_val : TB_sysex = 4144.
Proof. reflexivity. Qed.

(* image B's engine runs over the side stack (lib/AU/YCem.v aj_run_sh / aj_run_to_sh / aj_run_flag_sh) state their
   journal and their write-window goal through lib/AU/YCbqU.v, the shared plumbing through lib/Reusable/YCbq.v:
   cbe_jA turns every such journal in context into the latter form (CPgWalkU's cw_aj_of_U), cbe_awr such a goal
   (cw_awrA). *)
Ltac cbe_jA := repeat match goal with H : context [YCbqU.ajournal] |- _ => apply cw_aj_of_U in H end.

(* ================================ the payload and the result ================================ *)
(* the payload counter_encode builds at F + 32: pl[0] = counter_addr, pl[1] = dots, pl[2 + k] = seg[7 - k] *)
Definition cbe_pl (dc dots : Z) (seg : list Z) : list Z :=
[dc; dots; nth 7 seg 0; nth 6 seg 0; nth 5 seg 0; nth 4 seg 0; nth 3 seg 0; nth 2 seg 0; nth 1 seg 0; nth 0 seg 0].
Lemma cbe_pl_eq : forall dc dots seg, (8 <= length seg)%nat ->
[dc; dots] ++ rev (firstn 8 seg) = cbe_pl dc dots seg.
Proof.
intros dc dots seg Hl.
destruct seg as [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 seg']]]]]]]]; cbn [length] in Hl; try lia.
reflexivity.
Qed.
Lemma cbe_pl_len : forall dc dots seg, length (cbe_pl dc dots seg) = 10%nat.
Proof. reflexivity. Qed.
(* counter_encode's result is sysex_encode's on the payload, with the key KEY 6 counter_addr on success *)
Lemma cbe_spec_eq : forall d seg dots, (8 <= length seg)%nat ->
counter_spec (Some d) seg dots = with_key (sysex_spec (d_dev d) 48 (cbe_pl (d_counter d) dots seg)) (KEY 6 (d_counter d)).
Proof. intros d seg dots Hl. unfold counter_spec. rewrite (cbe_pl_eq _ _ _ Hl). reflexivity. Qed.
(* the payload as bytes of memory from its ten bytes *)
Lemma cbe_pl_garr8 : forall (m : word -> option byte) q dc dots seg,
0 <= dc < 256 -> 0 <= dots < 256 -> (forall j, (j < 8)%nat -> 0 <= nth j seg 0 < 256) ->
(forall j, (j < 10)%nat -> val_mem tfibsegs m (q + Z.of_nat j) 1 (nth j (cbe_pl dc dots seg) 0)) ->
garr8 tfibsegs m q (cbe_pl dc dots seg).
Proof.
intros m q dc dots seg Hdc Hdo Hs V j Hj. rewrite cbe_pl_len in Hj. split; [exact (V j Hj)|].
do 10 (destruct j as [|j]; [cbn [nth cbe_pl]; first [lia | apply Hs; lia] |]). lia.
Qed.
(* a 1-byte chunk read back: the low byte of a byte-valued atom, of its zero extension, of its sign extension *)
Lemma cbe_U_atom_mod : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 256 ->
bv_unsigned (sv_denot E (SOff k 0)) mod 2 ^ (8 * Z.of_N 1) = v.
Proof.
intros E k v Hk Hv. change (bv_unsigned (sv_denot E (SOff k 0))) with (U E (SOff k 0)).
rewrite (cw_U_atom0 E k v Hk) by lia. change (2 ^ (8 * Z.of_N 1)) with 256. apply Z.mod_small. exact Hv.
Qed.
(* the key, KEY 6 counter_addr, as the walk computes it (`or` with 0x60000) *)
Lemma cbe_lor_key : forall v, 0 <= v < 256 -> Z.lor v 393216 = v + 393216.
Proof.
intros v Hv.
assert (Hin : In v (map Z.of_nat (seq 0 256))) by (apply in_map_iff; exists (Z.to_nat v); split; [lia | apply in_seq; lia]).
assert (R : forallb (fun x => Z.eqb (Z.lor x 393216) (x + 393216)) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
apply Z.eqb_eq. exact (proj1 (forallb_forall _ _) R v Hin).
Qed.
Lemma cbe_key_val : forall v, 0 <= v < 256 -> KEY 6 v = v + 393216.
Proof.
intros v Hv. unfold KEY. change (6 * 65536) with 393216.
replace (Z.land v 0xffff) with v.
- rewrite Z.lor_comm. apply cbe_lor_key. exact Hv.
- symmetry. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
(* two ranges whose bytes have properties no byte has both of are apart *)
Lemma cbe_disj_pred : forall (P Q : Z -> Prop) q1 n1 q2 n2,
(forall a, q1 <= a < q1 + n1 -> P a) -> (forall a, q2 <= a < q2 + n2 -> Q a) -> (forall a, P a -> Q a -> False) ->
0 < n1 -> 0 < n2 -> q1 + n1 <= q2 \/ q2 + n2 <= q1.
Proof.
intros P Q q1 n1 q2 n2 HP HQ HPQ H1 H2.
destruct (Z_le_gt_dec (q1 + n1) q2) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (q2 + n2) q1) as [H3|H3]; [right; exact H3|].
exfalso. apply (HPQ (Z.max q1 q2)); [apply HP | apply HQ]; lia.
Qed.

(* ================================ arithmetic ================================ *)
(* `addi sp,sp,-128; andi sp,sp,-32` *)
Lemma cbe_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma cbe_count_cid_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c q] l IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.

(* ================================ the walk's write windows ================================ *)
(* The windows of the walk's states: the save area (atom 2, sp), the spill 16(s1) (atom 70, sp1), the frame
   (atom 75) and its shadow (atom 88), both the walk's own frame (0, pos), the head of the journal's own list. *)
Ltac cbe_fa :=
try (lazymatch goal with Hf : forall c p, frame_addr _ c p = frame_addr _ c p |- _ => rewrite ?Hf end);
try (unfold shadow_addr, SHADOW_OFF); rewrite ?unsigned_lit_small by lia; first [reflexivity | lia].
Ltac cbe_awr AG spv sp1v pos :=
idtac; cw_awrA;
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
    [reflexivity | evalE AG | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end
| lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (sp1v - sp0));
    [reflexivity | evalE AG | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end
| lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _ :: _) _ _ _ _ _ ?lyv _ =>
    eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ lyv _ 0 pos);
    [reflexivity | evalE AG; cbe_fa | left; reflexivity | apply Z.leb_le; vm_compute; reflexivity
    | apply Z.leb_le; vm_compute; reflexivity |] end
| lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _ :: _) _ _ _ _ _ ?lyv _ =>
    eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ lyv _ 0 pos);
    [reflexivity | evalE AG; cbe_fa | left; reflexivity
    | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |] end ];
lazymatch goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => fail 1 "cbe_awr: no rule for" r | _ => idtac end
end.
(* the engine's shadow table: the given entries SH0 (closed by tac0) and the app-memory entries of the state's
   writable windows *)
Ltac cbe_shok SH0 tac0 :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch goal with HS : st_ok ?segs ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
let SH := eval vm_compute in (SH0 ++ app_entries (ss_facts ss) (ss_mem ss)) in
let SHOK := fresh "SHOK" in
shok_assert SHOK segs CW_Bx SH Ex (mrestrict (w_H Wx) (ms_mem msx)) tac0 end.
Ltac cbe_shok0 :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch goal with HS : st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) |- _ =>
let SH := fresh "SHOK" in assert (SH : sh_ok tfibsegs CW_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by constructor end.
(* a rebase of the environment that carries env_agree 32 E0 E along *)
Ltac cbe_rebase HS AG HAE :=
let HEv := fresh "HEv" in
rebaseE HS AG HEv;
lazymatch type of HAE with env_agree 32 ?E0 _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let H2 := fresh "HAE" in
assert (H2 : env_agree 32 E0 Ev) by (rewrite HEv; env_agree_chain HAE);
clear HAE; rename H2 into HAE end end;
clear HEv.

(* ================================ the exit block 0x870fc ================================
   Live: sp = s1 = sp1 (70), gp, tp, s0 = sp (2), s2 = s8 = F (75), s9 = SB + F / 8 (88), and a0 = the result,
   the first of the fresh atoms 600.. (the other registers are dead and take the next ones); memory: the frame's
   shadow (88), the frame (75, the flag address at F + 56), the save area (2). *)
Definition cbe_X_deads : list nat := [10; 1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat.
Definition cbe_X_deads_bv : list (bv 5) := [10; 1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv.
Definition CBE_XN : nat := 600.
Definition cbe_saves : list YP09.chunk :=
[ YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
  YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Definition cbe_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 cbe_saves.
Definition cbe_frame : YP09.region := YP09.mkRegion (Some 75%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 87 0))].
Definition cbe_fsh : YP09.region := YP09.mkRegion (Some 88%nat) 0 8 0 8 [].
Definition cbe_X_atoms : list (nat * afact) :=
[ (88%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (87%nat, HPTR 0); (75%nat, HPTR 6);
  (70%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ].
Definition cbe_X_0 : sstate :=
mkSS B_CTR_EXIT
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 70 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
 SOff 75 0; SOff 88 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[ cbe_fsh; cbe_frame; cbe_stack ] None (mkFacts cbe_X_atoms [] []).
Definition ss_ctrX : sstate := Eval vm_compute in ss_havoc_regs cbe_X_0 CBE_XN cbe_X_deads.
(* A state at 0x870fc joined to ss_ctrX: the dead registers (a0 first) moved to the fresh atoms 600.., the regions
   cut to the frame, its shadow and the save area, the facts cut to cbe_X_atoms. *)
Ltac cbe_join HS :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let vals := eval cbv [map cbe_X_deads_bv] in (map (fun r => getr (ms_regs msv) r) cbe_X_deads_bv) in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_agree tfibsegs 600 Ev (havoc Ev 600 vals) ssv msv HS
    (env_agree_havoc_ge 600 600 Ev Ev vals (le_n _) (env_agree_refl 600 Ev)) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS;
  let rl := eval cbv [cbe_X_deads_bv] in cbe_X_deads_bv in
  set_regs_rec HS 600%nat vals 0%nat rl
end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_submem tfibsegs Ev ssv msv [cbe_fsh; cbe_frame; cbe_stack] HS
    ltac:(cbv [cbe_frame cbe_fsh cbe_stack cbe_saves]; cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS
end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_facts_incl3 tfibsegs Ev _ msv cbe_X_atoms [] [] HS
    ltac:(cbv [cbe_X_atoms]; cbn [ss_facts f_atoms]; incl_lit_tac)
    ltac:(let x := fresh "x" in intros x []) ltac:(let x := fresh "x" in intros x [])) as HS3;
  clear HS; rename HS3 into HS
end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  replace ssv with ss_ctrX in HS by (vm_compute; reflexivity) end.

(* a byte the caller's journal lets it write stays so with one more own frame *)
Lemma cbe_awr_byte_cons : forall STK sp0 FP bl0 blc ly own c a,
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (c :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own c a [H|[H|[H|(cid & ps & Hin & Hr)]]].
- left. exact H.
- right; left. exact H.
- right; right; left. exact H.
- right; right; right. exists cid, ps. split; [right; exact Hin | exact Hr].
Qed.

(* sysex_encode either fails without a command or succeeds with key 0 and at most 24 bytes *)
Lemma cbe_sysex_shape : forall dev fn pl,
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
Lemma cbe_with_key_none : forall rc k, with_key (rc, None) k = (rc, None).
Proof. intros [|q|q] k; reflexivity. Qed.
(* the command bytes of a success with the key replaced: the first 28 bytes, then the key's four *)
Lemma cbe_cmd_key : forall before bs dp k0 k, length before = 32%nat -> (length bs <= 24)%nat ->
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
Lemma cbe_cmd_len : forall before bs k dp, length before = 32%nat -> (length bs <= 24)%nat ->
length (cmd_outZ before (Some (bs, k, dp))) = 32%nat.
Proof.
intros before bs k dp Hb Hs. unfold cmd_outZ.
rewrite !app_length, map_length, skipn_length, !firstn_length, skipn_length. unfold le4Z. cbn [length]. lia.
Qed.
(* four bytes stored as a 4-byte value are its le4Z bytes *)
Lemma cbe_le4_garr8 : forall (m : word -> option byte) a v, 0 <= v < 2 ^ 32 ->
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
Lemma cbe_garr8_app : forall (m : word -> option byte) a l1 l2,
garr8 tfibsegs m a l1 -> garr8 tfibsegs m (a + Z.of_nat (length l1)) l2 -> garr8 tfibsegs m a (l1 ++ l2).
Proof.
intros m a l1 l2 G1 G2 j Hj. rewrite app_length in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [H|H].
- rewrite app_nth1 by exact H. exact (G1 j H).
- rewrite app_nth2 by exact H. destruct (G2 (j - length l1)%nat ltac:(lia)) as (V & Hb). split; [|exact Hb].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact V.
Qed.
Lemma cbe_garr8_firstn : forall (m : word -> option byte) a l n, garr8 tfibsegs m a l -> garr8 tfibsegs m a (firstn n l).
Proof.
intros m a l n G j Hj. rewrite firstn_length in Hj. rewrite nth_firstn.
replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply G. lia.
Qed.

Lemma cbe_awr_byte_mono : forall STK sp0 FP bl0 blc blc' ly ly' own own' a,
awr_byte STK sp0 FP bl0 blc ly own a ->
(forall b m, In (b, m) blc -> In (b, m) blc') -> incl own own' -> (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a [H|[(H1 & bb & mm & Hin & Hr)|[(bb & mm & Hin & Hn & Hr)|(cid & ps & Hin & Hr)]]] Hb Hown Efa.
- left. exact H.
- right; left. split; [exact H1|]. exists bb, mm. split; [exact (Hb bb mm Hin) | exact Hr].
- right; right; left. exists bb, mm. split; [exact (Hb bb mm Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, ps. split; [exact (Hown _ Hin)|]. rewrite !Efa. exact Hr.
Qed.

(* bytes off every write window of a run keep their values *)
Lemma cbe_garr8_run : forall (Ev : env) rs H (m1 m2 : word -> option byte) (Zn : Z -> Prop) q l,
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

(* ================================ the frame's zone ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* A frame position the call state does not hold is the runtime's own there: its bytes and its shadow
   (YF0v own_free_frame / own_free_frame_shadow), with the position's bounds from the state that holds it. *)
Lemma cbe_fz_owned : forall lyc Sc (W : world tfibsegs) memc mdc S2 (W2 : world tfibsegs) m2 md2 pos a,
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
Lemma cbe_hull_tdst : forall ly S (W : world tfibsegs) mem md q n,
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
Lemma cbe_ra_tdst : forall lyc Sc (W : world tfibsegs) memc mdc ly1 S1 (W1 : world tfibsegs) m1 md1 q n,
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
Lemma cbe_tcj_mono : forall T lyc Sc (W : world tfibsegs) m (W2 : world tfibsegs) m2 sp (E E' : Z -> Prop),
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
Lemma cbe_tdst_not_owned : forall ly S (W : world tfibsegs) mem md q n a,
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
Definition cbe_wz (sp : Z) (lyc : alayout) (pos a : Z) : Prop :=
(sp - TB_counter <= a < sp) \/ in_zr a (frame_rng lyc (0, pos)) \/
in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8).
(* The walk's kept invariant through a run whose writes lie in the window or in the walk's own frame. *)
Lemma cbe_kt_run : frame_flag_lawP tfibsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k ly2 S2 (W2 : world tfibsegs) m2 md2 k2 pos sp
(E X : Z -> Prop) (W1 : world tfibsegs) m1 m3,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) ly2 S2 W2 m2 md2 k2 ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> alloc_ceiling <= sp - TB_counter ->
tcj_kept tfibsegs B TB_counter lyc Sc W memc W1 m1 sp E ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H W1) m3 a = aview tfibsegs (w_H W1) m1 a) ->
(forall a, X a -> cbe_wz sp lyc pos a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m3 a) ->
tcj_kept tfibsegs B TB_counter lyc Sc W memc W1 m3 sp E.
Proof.
intros FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 m2 md2 k2 pos sp E X W1 m1 m3
HJ0 HJ2 HP Hce KT HX HXc Hpr.
apply (cw_kept_step B LAWS TB_counter lyc Sc W memc mdc W1 m1 m3 sp E X Hce (proj1 HJ0) KT HX); [|exact Hpr].
intros a Hx. destruct (HXc a Hx) as [Hw | Hf]; [left; exact Hw|].
right; right. apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 m2 md2 k2 0 pos a HJ0 HJ2 HP).
destruct Hf as [Hf | Hf]; [left; exact Hf | right; left; exact Hf].
Qed.
(* The values of the bytes that are neither the runtime's own in the call state nor in the window. *)
Definition cbe_ka (lyc : alayout) (Sc : astate) (sp : Z) (H : word -> bool) (m m0 : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (aowned B lyc Sc a \/ sp - TB_counter <= a < sp) -> aview tfibsegs H m a = aview tfibsegs H m0 a.
Lemma cbe_ka_run : forall lyc Sc (W : world tfibsegs) memc mdc S2 (W2 : world tfibsegs) m2 md2 pos sp (X : Z -> Prop) H m1 m3 m0,
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B lyc S2 W2 m2 md2 -> In (0, pos) (frames S2) -> ~ In (0, pos) (frames Sc) ->
cbe_ka lyc Sc sp H m1 m0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs H m3 a = aview tfibsegs H m1 a) ->
(forall a, X a -> cbe_wz sp lyc pos a) ->
cbe_ka lyc Sc sp H m3 m0.
Proof.
intros lyc Sc W memc mdc S2 W2 m2 md2 pos sp X H m1 m3 m0 HAR HAR2 Hin Hnin KA HX HXc a Ha Hn.
rewrite (HX a Ha); [exact (KA a Ha Hn)|].
intros Hx. apply Hn. destruct (HXc a Hx) as [Hw | Hf]; [right; exact Hw|].
left. exact (cbe_fz_owned lyc Sc W memc mdc S2 W2 m2 md2 pos a HAR HAR2 Hin Hnin Hf).
Qed.
(* the same through a run that writes only the window *)
Lemma cbe_ka_run0 : forall lyc Sc sp (X : Z -> Prop) H m1 m3 m0,
cbe_ka lyc Sc sp H m1 m0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs H m3 a = aview tfibsegs H m1 a) ->
(forall a, X a -> sp - TB_counter <= a < sp) ->
cbe_ka lyc Sc sp H m3 m0.
Proof.
intros lyc Sc sp X H m1 m3 m0 KA HX HXc a Ha Hn.
rewrite (HX a Ha); [exact (KA a Ha Hn)|]. intros Hx. apply Hn. right. exact (HXc a Hx).
Qed.
(* the bytes of an object in blocks or frames of the call state, kept by a walk that writes no such byte *)
Lemma cbe_garr8_kept : forall T lyc Sc (W : world tfibsegs) memc (W1 : world tfibsegs) m1 sp q l,
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
Lemma cbe_tdst_below : forall lyc Sc (W : world tfibsegs) memc mdc q n,
AR tfibsegs B lyc Sc W memc mdc -> tdst_ok B lyc Sc q n -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof.
intros lyc Sc W memc mdc q n HAR Hd Hn.
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc q n q HAR Hd ltac:(lia)) as (H1 & _).
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc q n (q + n - 1) HAR Hd ltac:(lia)) as (H2 & _).
lia.
Qed.
Lemma cbe_tdst_of_cobj : forall lyc Sc q n, cobj_ok B lyc Sc q n -> tdst_ok B lyc Sc q n.
Proof.
intros lyc Sc q n [(bb & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] a Ha.
- left. exists bb, m. split; [exact Hin | lia].
- right. exists cid, pos. split; [exact Hin|]. unfold frame_rng, in_zr. cbn [fst snd]. lia.
Qed.
Lemma cbe_tdst_sub : forall lyc Sc q n q' n', tdst_ok B lyc Sc q n -> q <= q' -> q' + n' <= q + n -> tdst_ok B lyc Sc q' n'.
Proof. intros lyc Sc q n q' n' Hd H1 H2 a Ha. apply Hd. lia. Qed.
(* a range of fresh bytes is apart from an object in blocks or frames of the call state *)
Lemma cbe_fresh_disj2 : forall lyc Sc q n x m, tdst_ok B lyc Sc q n ->
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
Lemma cbe_tdst_req : forall lyc Sc S2 c q n, tdst_ok B lyc Sc q n ->
ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = c :: frames Sc -> tdst_ok B lyc S2 q n.
Proof.
intros lyc Sc S2 c q n Hd Eab Hfr a Ha.
destruct (Hd a Ha) as [(bb & mm & Hin & Hr) | (cid & ps & Hin & Hr)].
- left. exists bb, mm. rewrite Eab. split; [exact Hin | exact Hr].
- right. exists cid, ps. rewrite Hfr. split; [right; exact Hin | exact Hr].
Qed.
(* a byte of a heap block or of a live frame of a state is present *)
Lemma cbe_tdst_present : forall ly S (W : world tfibsegs) mem md q n a,
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
Lemma cbe_cdst_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k S2 pos m md sp sp1 out,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W m md k ->
ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = (0, pos) :: frames Sc ->
tcj_kept tfibsegs B TB_counter lyc Sc W memc W m sp (fun _ => False) ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp TB_counter out 32 ->
alloc_ceiling <= sp - TB_counter -> sp - 144 <= sp1 <= sp ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc S2 ((0, pos) :: own) W m sp1 TB_sysex out 32.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 pos m md sp sp1 out HJ0 HJ Eab Hfr KT
(Hq0 & Hq63 & Htd & Htw & Hra & Hhull & Ham & Hwin) Hce Hsp1.
pose proof KT as (_ & _ & _ & K4 & _).
pose proof (cbe_tdst_req lyc Sc S2 (0, pos) out 32 Htd Eab Hfr) as Htd2.
pose proof (proj1 HJ0) as HAR. pose proof (proj1 HJ) as HAR2.
unfold TB_counter, TB_sysex, ESTACK in *.
split; [lia|]. split; [lia|]. split; [exact Htd2|].
split.
{ intros a Ha. destruct (Htw a Ha) as (Haw & _ & _ & _).
  pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 a HAR Htd Ha) as (Hb1 & _).
  split; [rewrite Eab; apply cbe_awr_byte_cons; exact Haw|].
  split; [exact (cbe_tdst_present lyc S2 W m md out 32 a HAR2 Htd2 Ha)|].
  split; [exact (cbe_tdst_not_owned lyc S2 W m md out 32 a HAR2 Htd2 Ha)|].
  unfold ESTACK. lia. }
split.
{ apply (cbe_ra_tdst lyc Sc W memc mdc lyc S2 W m md out 32 HAR HAR2 Htd).
  - intros bb mm Hin. rewrite Eab. exact Hin.
  - intros cid ps a Hin Hr. exact (K4 cid ps a Hin (or_intror Hr) (fun H => H)).
  - exact Hra. }
split; [intros _; apply (cbe_hull_tdst lyc S2 W m md out 32 HAR2 Htd2); lia|].
split; [exact Ham|].
left. pose proof (cbe_tdst_below lyc Sc W memc mdc out 32 HAR Htd ltac:(lia)). lia.
Qed.
(* an object of a state is one of a later state with more blocks and frames at the same addresses *)
Lemma cbe_tdst_mono : forall lyc Sc ly4 S4 q n, tdst_ok B lyc Sc q n ->
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
