(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 571 of its 623 lines of code are new or changed and 462 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T6 (CRT-B-L3): the SYMBOLIC STATE of the member loop
   (B' entry + 0x5b4 .. + 0x6f4), split off Crt102B_T6.v so the walk
   recompiles alone.

   proves no function (kind: segment lemma support).

   WHAT IS HERE: the member loop's symbolic state ct6_ssx (one state serves the three cuts L3 = +0x5b4, K = +0x64c after
   the key compare, R = +0x6d0 after the value compare, and M = +0x6d4: the loop writes no memory, so only the cut's own
   extra facts change), the image-free reader facts it needs (the i-th member of an object, the object header, the
   shadow of a block), and ct6_entry: crt_at_L3_B (the frozen glue's, lib/A/Prog/Crt102Glue.v) gives that state at any
   pc and the member's data (key strings, value nodes, the blocks they lie in).

   KB ROUND (the wild budget, Crt102Glue.v's G3 / G4): crt_at_L3_B's live state is at kb = prh_wk F_check_round_trip
   (the notation liveB carries it) and its journal at a budget WS with wbudget [] (prh_wk F_check_round_trip) WS;
   ct6_entry reads the journal at that WS (Crt102KitB.cb4_ff takes any WS). No statement of this file changed.

   INPUTS OF RECORD (taken by path):
   - base commit cbe6d10993c2 (candidate base) (Crt102Glue.v with the frozen crt_at_L3_B /
     crt_at_C_B / CRT_B_SEG_T6, Crt102Img.v, Crt102Model.v; lib/B/Prog/Crt102KitB.v: cb4_sp, cb4_ff, cb4_doc_home,
     cb4_ar0, cb4_fb).
   - listing lib/B/Listing_prog.v 8bcc2c9e7809 (listing commit d42e123915ae).

   NUMERALS. DERIVED: the inner pcs 0x650 / 0x6d4 (4 * the slot inside the function, the listing), the atom indices of
   the symbolic state (the engine's numbering: 32 + register, 64 + extra). LENGTH: the spill offsets off s1 (the glue's
   CRT_SP_ names), 24 / 32 / 40 (kids / keys / n inside struct pj), 8 / 56 (the loop's strides), 16 (cf_head),
   2 ^ 44 / 2 ^ 47 / 2 ^ 50 / 2 ^ 23 (address bounds). WORD: register indices. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck PRH_FnEx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ======================================================================================================== *)
(* PART 0: the inner cuts and the symbolic state the three stretches start from (closed terms).
   Atoms: 32 + r the current register r (S10Env.v TE); the extras 64 .. 76 (ct6_more below):
   64 doc, 65 back.keys, 66 doc->keys, 67 back.keys + 8 i, 68 doc->keys + 8 i, 69 back.keys[i], 70 doc->keys[i],
   71 back.kids, 72 doc->kids, 73 back.kids + 56 i, 74 doc->kids + 56 i, 75 doc->n, 76 at. Registers: 41 = x9 = s1,
   51 = x19 = F, 53 = x21 = i, 56 = x24 = 8 i, 58 = x26 = 56 i, 59 = x27 = the shadow base; x22 holds shadow (&doc->keys). *)
Definition CRT_K_OFF6_B : Z := 0x650.   (* +0x650: `ld a0, 0x40(s1)`, after the key compare *)
Definition CRT_M_OFF6_B : Z := 0x6d4.   (* +0x6d4: `ld a0, 0x50(s1)`, after the value compare (or the skip) *)
Lemma crt_cuts_T6_B :
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_K_OFF6_B) = Some (PW 0x404b503) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_M_OFF6_B) = Some (PW 0x504b503) /\
  CRT_L3_OFF_B = 0x5b4 /\ CRT_C_OFF_B = 0x6f8.
Proof. vm_compute. repeat split. Qed.

Definition ct6_shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 59 0).
Definition ct6_regs : list sv := sr_set cur_atoms 22%bv (ct6_shx 64 32).
Definition ct6_s1 : YP09.region := YP09.mkRegion (Some 41%nat) 0 96 0 0
  [YP09.mkChunk 40 (CVal 8 (ct6_shx 64 24)); YP09.mkChunk 48 (CVal 8 (SOff 64 32));
   YP09.mkChunk 56 (CVal 8 (SOff 51 32)); YP09.mkChunk 64 (CVal 8 (SOff 76 0));
   YP09.mkChunk 72 (CVal 8 (SOff 64 24)); YP09.mkChunk 80 (CVal 8 (ct6_shx 64 40));
   YP09.mkChunk 88 (CVal 8 (SOff 64 40))].
Definition ct6_back : YP09.region := YP09.mkRegion (Some 51%nat) 56 72 0 0
  [YP09.mkChunk 56 (CVal 8 (SOff 71 0)); YP09.mkChunk 64 (CVal 8 (SOff 65 0))].
Definition ct6_doc : YP09.region := YP09.mkRegion (Some 64%nat) 24 48 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 72 0)); YP09.mkChunk 32 (CVal 8 (SOff 66 0)); YP09.mkChunk 40 (CVal 8 (SOff 75 0))].
Definition ct6_kb : YP09.region := YP09.mkRegion (Some 67%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 69 0))].
Definition ct6_kd : YP09.region := YP09.mkRegion (Some 68%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 70 0))].
Definition ct6_mem : smem := [ct6_s1; ct6_back; ct6_doc; ct6_kb; ct6_kd].
Definition CT6_HI : Z := 2 ^ 47 - 2 ^ 23.
Definition ct6_atoms : list (nat * afact) :=
  [(59%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (41%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (51%nat, mkAF 4096 CT6_HI 5);
   (53%nat, mkAF 0 (2 ^ 44) 0); (56%nat, mkAF 0 (2 ^ 47) 3); (58%nat, mkAF 0 (2 ^ 50) 3);
   (64%nat, mkAF 4096 CT6_HI 3); (65%nat, mkAF 4096 CT6_HI 4); (66%nat, mkAF 4096 CT6_HI 4);
   (67%nat, mkAF 4096 CT6_HI 3); (68%nat, mkAF 4096 CT6_HI 3);
   (69%nat, mkAF 4096 CT6_HI 4); (70%nat, mkAF 4096 CT6_HI 4);
   (71%nat, mkAF 4096 CT6_HI 4); (72%nat, mkAF 4096 CT6_HI 4);
   (73%nat, mkAF 4096 CT6_HI 3); (74%nat, mkAF 4096 CT6_HI 3);
   (75%nat, mkAF 1 (2 ^ 44) 0); (76%nat, mkAF 0 (2 ^ 44) 0)].
Definition ct6_conds : list acond :=
  [mkAC BC_LTU (SOff 53 0) (SOff 75 0);
   mkAC BC_GEU (SOff 67 0) (SOff 65 0); mkAC BC_GEU (SOff 68 0) (SOff 66 0);
   mkAC BC_GEU (SOff 73 0) (SOff 71 0); mkAC BC_GEU (SOff 74 0) (SOff 72 0)].
Definition ct6_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 65 0) (SOff 56 0), SOff 67 0); (SAlu ALU_ADD (SOff 66 0) (SOff 56 0), SOff 68 0);
   (SAlu ALU_ADD (SOff 71 0) (SOff 58 0), SOff 73 0); (SAlu ALU_ADD (SOff 72 0) (SOff 58 0), SOff 74 0);
   (SAlu ALU_SUB (SAlu ALU_SLL (SOff 53 0) (SLit 6)) (SAlu ALU_SLL (SOff 53 0) (SLit 3)), SOff 58 0);
   (SAlu ALU_SRL (SOff 53 0) (SLit 60), SLit 0); (SAlu ALU_SRA (SOff 58 0) (SLit 63), SLit 0);
   (SAlu ALU_XOR (SMd M_MULH (SOff 53 0) (SLit 56)) (SLit 0), SLit 0)].
(* the state at a cut, with the cut's own extra atom facts xa and conditions xc in front (a0 after a call, the
   branch a run must not fork on) *)
Definition ct6_ssx (pc : Z) (xa : list (nat * afact)) (xc : list acond) : sstate :=
  mkSS pc ct6_regs ct6_mem None (mkFacts (xa ++ ct6_atoms) (xc ++ ct6_conds) ct6_alias).
Definition ct6_SH : list shent := [mkSHE 64 0 56; mkSHE 67 0 8; mkSHE 68 0 8].
Definition ct6_Bx : sv := SOff 59 0.
Definition ct6_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ct6_more (doc kb kd xb xd kib kid nn atv : Z) (i : nat) : list word :=
  [w64 doc; w64 kb; w64 kd; w64 (kb + 8 * Z.of_nat i); w64 (kd + 8 * Z.of_nat i); w64 xb; w64 xd;
   w64 kib; w64 kid; w64 (kib + 56 * Z.of_nat i); w64 (kid + 56 * Z.of_nat i); w64 nn; w64 atv].

(* ======================================================================================================== *)
(* PART 1, image-free helpers *)
Lemma ct6_ra_of_bshadow : forall (rd : Z -> option Z) p n x len,
  block_shadow rd SHADOW_OFF p n -> p <= x -> x + len <= p + n -> range_addressable rd SHADOW_OFF x len.
Proof.
intros rd p n x len (Hp & Hn & Hb) Hx Hxl y Hy.
assert (Ep : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
set (i := (y - p) / 8).
assert (Hi0 : 0 <= i) by (apply Z.div_pos; lia).
assert (Ey : y / 8 = p / 8 + i).
{ unfold i. replace y with ((p / 8) * 8 + (y - p)) at 1 by lia. rewrite Z.div_add_l by lia. reflexivity. }
assert (Hi : i < (n + 7) / 8).
{ unfold i. apply Z.div_lt_upper_bound; [lia|].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia. }
pose proof (Hb i (conj Hi0 Hi)) as Hs. unfold shadow_of_addr in *. rewrite Ey, Z.add_assoc.
eexists. split; [exact Hs|].
destruct (Z.ltb_spec i (n / 8)) as [Hl|Hl]; [left; reflexivity|right].
pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mn.
pose proof (Z.div_mod (y - p) 8 ltac:(lia)) as Dy. pose proof (Z.mod_pos_bound (y - p) 8 ltac:(lia)) as My.
fold i in Dy.
assert (Ei : i = n / 8) by lia.
assert (Hym : y mod 8 = (y - p) mod 8).
{ rewrite Ep. replace (y - 8 * (p / 8)) with (y + (- (p / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite Hym. lia.
Qed.

Lemma ct6_hull_sub : forall (rd : Z -> option Z) x n y m,
  shadow_hull_vis rd x n -> x <= y -> y + m <= x + n -> 0 < m -> shadow_hull_vis rd y m.
Proof.
intros rd x n y m H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : (SHADOW_OFF + x / 8) / 8 * 8 <= (SHADOW_OFF + y / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (A2 : (SHADOW_OFF + (y + m - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

Lemma ct6_pairwise_neq : forall {X} (R : X -> X -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y ->
  R x y \/ R y x.
Proof.
intros X R l. induction l as [|a l IH]; intros x y P Hx Hy Ne; [destruct Hx|]. destruct P as [F P].
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- exfalso. exact (Ne eq_refl).
- left. exact (proj1 (Forall_forall _ _) F y Hy).
- right. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y P Hx Hy Ne).
Qed.

(* the i-th member of an object: its key word, its key string and its value node, all inside the object's blocks *)
Lemma ct6_mems_nth : forall segs m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  pj_memsR segs m lblk P a ka l D -> nth_error l i = Some (nm, u) ->
  exists x k D1, rd_u64 segs m (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m lblk x k nm /\
    P (a + 56 * Z.of_nat i) u D1 /\ In (x, k) D /\ incl D1 D.
Proof.
intros segs m lblk P l. induction l as [|[nm0 u0] l IH]; intros a ka D i nm u H Hi; [destruct i; discriminate|].
cbn [pj_memsR] in H. destruct H as (x & k & D1 & D2 & ED & Hx & Hc & HP & HR).
destruct i as [|i]; cbn [nth_error] in Hi.
- injection Hi as <- <-. exists x, k, D1. rewrite !Z.mul_0_r, !Z.add_0_r.
  split; [exact Hx|]. split; [exact Hc|]. split; [exact HP|]. subst D. split; [left; reflexivity|].
  intros b Hb. right. apply in_or_app. left. exact Hb.
- destruct (IH (a + 56) (ka + 8) D2 i nm u HR Hi) as (x' & k' & D1' & Hx' & Hc' & HP' & Hin' & Hinc').
  exists x', k', D1'. rewrite Nat2Z.inj_succ.
  replace (ka + 8 * Z.succ (Z.of_nat i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.succ (Z.of_nat i)) with (a + 56 + 56 * Z.of_nat i) by lia.
  split; [exact Hx'|]. split; [exact Hc'|]. split; [exact HP'|]. subst D.
  split; [right; apply in_or_app; right; exact Hin'|].
  intros b Hb. right. apply in_or_app. right. exact (Hinc' b Hb).
Qed.

(* the header of a non-empty object node *)
Lemma ct6_obj_hdr : forall segs m lblk p ms D,
  pj_nodeR segs m lblk p (PjTree.JObj ms) D -> (0 < length ms)%nat ->
  exists kids keys cap Di,
    rd_u64 segs m (p + 24) kids /\ rd_u64 segs m (p + 32) keys /\ rd_u64 segs m (p + 40) (Z.of_nat (length ms)) /\
    p mod 8 = 0 /\ Z.of_nat (length ms) <= cap /\ lblk kids (56 * cap) /\ lblk keys (8 * cap) /\
    D = [(kids, 56 * cap); (keys, 8 * cap)] ++ Di /\ NoDup D /\
    pj_memsR segs m lblk (pj_nodeR segs m lblk) kids keys ms Di.
Proof.
intros segs m lblk p ms D H Hl. cbn [pj_nodeR] in H.
destruct H as (Hnd & _ & num & str & kids & keys & n & cap & Hh & _ & En & Hc & Hcap & Di & ED & Hm).
destruct Hcap as [(Hc0 & _ & _) | (Hc0 & Lk & Ly)]; [lia|].
rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
destruct Hh as ((Hp8 & _) & _ & _ & _ & Hkids & Hkeys & Hn & _).
exists kids, keys, cap, Di. rewrite <- En.
split; [exact Hkids|]. split; [exact Hkeys|]. split; [exact Hn|]. split; [exact Hp8|]. split; [lia|].
split; [exact Lk|]. split; [exact Ly|]. split; [exact ED|]. split; [exact Hnd | exact Hm].
Qed.

Lemma ct6_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2. induction l1 as [|[n f] l1 IH]; cbn [app atoms_ok]; [tauto|]. intros [H1 H2] H3. exact (conj H1 (IH H2 H3)). Qed.
Lemma ct6_conds_app : forall E l1 l2, conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof. intros E l1 l2. induction l1 as [|c l1 IH]; cbn [app conds_ok]; [tauto|]. intros [H1 H2] H3. exact (conj H1 (IH H2 H3)). Qed.
Lemma ct6_denot_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n c x H Hx Hxc. apply bv_eq. rewrite denot_SOff, H, !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ct6_denot_at : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 x.
Proof.
intros E n x H Hx. apply bv_eq. rewrite denot_SOff, H, !unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id.
unfold M64. lia.
Qed.

Lemma ct6_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.

(* the denotation of the shadow address the code forms (`srli x, a, 3; add x, x, s11`) *)
Lemma ct6_shx_denot : forall E n c a, ew E n = Z_to_bv 64 a -> ew E 59 = Z_to_bv 64 SHADOW_OFF ->
  0 <= a < 2 ^ 47 -> 0 <= a + c < 2 ^ 47 -> sv_denot E (ct6_shx n c) = Z_to_bv 64 (shadow_addr (a + c)).
Proof.
intros E n c a Hn H59 Ha Hac. apply bv_eq.
change (bv_unsigned (sv_denot E (ct6_shx n c))) with (U E (ct6_shx n c)). unfold ct6_shx.
rewrite !U_SAlu, !U_SOff, U_SLit, Hn, H59.
assert (Hd : 0 <= (a + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite !unsigned_lit_small by (cbv [shadow_addr SHADOW_OFF]; lia).
unfold zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
rewrite (Z.mod_small 3) by lia. change (Z.land 3 63) with 3.
rewrite Z.add_0_r, (Z.mod_small (a + c)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite !Z.mod_small; lia.
Qed.

(* ======================================================================================================== *)
(* PART 2, image B' at the B instance (lib/B/PAImg_prog.v PI_prog_B, PL_prog_B) *)
Section t6. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* a harness block of the ledger at the current state: where it lies, its shadow and hull, its bytes present *)
Lemma ct6_blk : forall lyc Sc Hpc Wc memc mdc Lamc peakc cntc ranc {mostc ownc : Z} a k,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc mostc ownc -> In (a, k) Lamc ->
  0 <= k /\ a mod 16 = 0 /\ 4096 + 16 <= a /\ a + k <= YM05.alloc_ceiling /\ in_app a k /\
  In (a - 16, k + 16) (ablocks B lyc Sc) /\
  (forall y n, a <= y -> 0 <= n -> y + n <= a + k -> range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF y n) /\
  (forall y n, a <= y -> 0 < n -> y + n <= a + k -> shadow_hull_vis (aview SEGS (w_H Wc) memc) y n) /\
  (forall y, a <= y < a + k -> apresent (w_H Wc) memc y).
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc ranc mostc ownc a k HAR HLED Hin.
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k mostc ownc HLED Hin)
  as (Hk0 & Hab & Hhp & H16 & _).
rewrite Hch16 in Hab, Hhp.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hab) as (Hm16 & H4096 & Hce & Happ & Hpres & _).
destruct (alx_hshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hab Hhp) as (Hbs & Hhull).
assert (Erq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hch16, Erq in Hbs, Hhull. rewrite Erq in Hce, Happ, Hpres.
replace (a - 16 + 16) with a in Hbs, Hhull by lia. replace (k + 16 - 16) with k in Hbs, Hhull by lia.
split; [exact Hk0|]. split; [exact H16|]. split; [lia|]. split; [lia|].
split; [apply (in_app_sub _ _ _ _ Happ); lia|]. split; [exact Hab|].
split; [intros y n Hy Hn Hyn; exact (ct6_ra_of_bshadow _ a k y n Hbs Hy Hyn)|].
split; [intros y n Hy Hn Hyn; apply (ct6_hull_sub _ a k y n); [apply Hhull; lia | lia | lia | lia]|].
intros y Hy. exact (proj1 (Hpres y ltac:(lia))).
Qed.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
(* tcheck_round_trip_specX's premises at the entry (PRH_FnCheck.v, the text's own; Crt102Top discharges them) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc)
  (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most) (prh_wk F_check_round_trip)).
#[local] Notation L3B := (crt_at_L3_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation CB := (crt_at_C_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).
#[local] Notation spillB := (crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation tcB := (crt_tc (t := t)).

(* ---- the symbolic state at L3 / K / M from concrete facts ---- *)
Lemma ct6_st_ok : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg sp1v F doc' kb kd xb xd kib kid nn atv
    capb capd (i : nat),
  getr rg 9 = w64 sp1v -> getr rg 19 = w64 F -> getr rg 21 = w64 (Z.of_nat i) -> getr rg 24 = w64 (8 * Z.of_nat i) ->
  getr rg 26 = w64 (56 * Z.of_nat i) -> getr rg 27 = w64 SHADOW_OFF -> getr rg 22 = w64 (shadow_addr (doc' + 32)) ->
  YM05.alloc_ceiling <= sp1v <= 2 ^ 47 -> sp1v mod 32 = 0 ->
  4096 <= F -> F + 512 <= YM05.alloc_ceiling -> F mod 32 = 0 ->
  4096 <= doc' -> doc' + 56 <= YM05.alloc_ceiling -> doc' mod 8 = 0 ->
  4096 <= kb -> kb + 8 * capb <= YM05.alloc_ceiling -> kb mod 16 = 0 ->
  4096 <= kd -> kd + 8 * capd <= YM05.alloc_ceiling -> kd mod 16 = 0 ->
  4096 <= kib -> kib + 56 * capb <= YM05.alloc_ceiling -> kib mod 16 = 0 ->
  4096 <= kid -> kid + 56 * capd <= YM05.alloc_ceiling -> kid mod 16 = 0 ->
  4096 <= xb <= YM05.alloc_ceiling -> xb mod 16 = 0 -> 4096 <= xd <= YM05.alloc_ceiling -> xd mod 16 = 0 ->
  (Z.of_nat i < nn)%Z -> nn <= capd -> nn <= capb -> 1 <= nn -> 0 <= atv <= nn ->
  (* the five regions are pairwise apart *)
  (F + 72 <= doc' + 24 \/ doc' + 48 <= F + 56) ->
  (F + 72 <= kb + 8 * Z.of_nat i \/ kb + 8 * Z.of_nat i + 8 <= F + 56) ->
  (F + 72 <= kd + 8 * Z.of_nat i \/ kd + 8 * Z.of_nat i + 8 <= F + 56) ->
  (doc' + 48 <= kb + 8 * Z.of_nat i \/ kb + 8 * Z.of_nat i + 8 <= doc' + 24) ->
  (doc' + 48 <= kd + 8 * Z.of_nat i \/ kd + 8 * Z.of_nat i + 8 <= doc' + 24) ->
  (kb + 8 * Z.of_nat i + 8 <= kd + 8 * Z.of_nat i \/ kd + 8 * Z.of_nat i + 8 <= kb + 8 * Z.of_nat i) ->
  (* the chunks *)
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 40) 8 (shadow_addr (doc' + 24)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 48) 8 (doc' + 32) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 56) 8 (F + 32) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 64) 8 atv ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 72) 8 (doc' + 24) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 80) 8 (shadow_addr (doc' + 40)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 88) 8 (doc' + 40) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 56) 8 kib -> val_mem SEGS (mrestrict (w_H Wc) memc) (F + 64) 8 kb ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (doc' + 24) 8 kid -> val_mem SEGS (mrestrict (w_H Wc) memc) (doc' + 32) 8 kd ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (doc' + 40) 8 nn ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (kb + 8 * Z.of_nat i) 8 xb ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (kd + 8 * Z.of_nat i) 8 xd ->
  (* the shadow entries *)
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc' 56 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (kb + 8 * Z.of_nat i) 8 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (kd + 8 * Z.of_nat i) 8 ->
  in_app doc' 56 -> in_app (kb + 8 * Z.of_nat i) 8 -> in_app (kd + 8 * Z.of_nat i) 8 ->
  forall xa xc, atoms_ok (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) xa ->
  conds_ok (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) xc ->
  st_ok_pi SEGS VAL (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) (ct6_ssx pc xa xc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS ct6_Bx ct6_SH (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) (mrestrict (w_H Wc) memc).
Proof.
intros fxk pc Wc memc rg sp1v F doc' kb kd xb xd kib kid nn atv capb capd i
  R9 R19 R21 R24 R26 R27 R22 Hs1 Hs1a HF1 HF2 HF3 Hd1 Hd2 Hd3 Hkb1 Hkb2 Hkb3 Hkd1 Hkd2 Hkd3
  Hib1 Hib2 Hib3 Hid1 Hid2 Hid3 Hxb Hxb16 Hxd Hxd16 Hin Hnd Hnb Hn1 Hat
  DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 C40 C48 C56 C64 C72 C80 C88 CB56 CB64 CD24 CD32 CD40 CKB CKD RAd RAkb RAkd APd APkb APkd
  xa xc XA XC.
set (mo := ct6_more doc' kb kd xb xd kib kid nn atv i).
set (E := TEB regs rg mo).
assert (HIc : CT6_HI = 2 ^ 47 - 2 ^ 23) by reflexivity.
pose proof (YM05.alloc_ceiling_val) as Hac.
assert (Ei : 0 <= Z.of_nat i) by lia.
assert (Hi44 : Z.of_nat i < 2 ^ 44) by lia.
(* the atoms' values *)
assert (A41 : ew E 41 = w64 sp1v) by exact (eq_trans (te_cur regs rg mo 9%bv 9 eq_refl) R9).
assert (A51 : ew E 51 = w64 F) by exact (eq_trans (te_cur regs rg mo 19%bv 19 eq_refl) R19).
assert (A53 : ew E 53 = w64 (Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 21%bv 21 eq_refl) R21).
assert (A56 : ew E 56 = w64 (8 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 24%bv 24 eq_refl) R24).
assert (A58 : ew E 58 = w64 (56 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 26%bv 26 eq_refl) R26).
assert (A59 : ew E 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (A64 : ew E 64 = w64 doc') by exact (te_more_lt regs rg mo 0 ltac:(lia)).
assert (A65 : ew E 65 = w64 kb) by exact (te_more_lt regs rg mo 1 ltac:(lia)).
assert (A66 : ew E 66 = w64 kd) by exact (te_more_lt regs rg mo 2 ltac:(lia)).
assert (A67 : ew E 67 = w64 (kb + 8 * Z.of_nat i)) by exact (te_more_lt regs rg mo 3 ltac:(lia)).
assert (A68 : ew E 68 = w64 (kd + 8 * Z.of_nat i)) by exact (te_more_lt regs rg mo 4 ltac:(lia)).
assert (A69 : ew E 69 = w64 xb) by exact (te_more_lt regs rg mo 5 ltac:(lia)).
assert (A70 : ew E 70 = w64 xd) by exact (te_more_lt regs rg mo 6 ltac:(lia)).
assert (A71 : ew E 71 = w64 kib) by exact (te_more_lt regs rg mo 7 ltac:(lia)).
assert (A72 : ew E 72 = w64 kid) by exact (te_more_lt regs rg mo 8 ltac:(lia)).
assert (A73 : ew E 73 = w64 (kib + 56 * Z.of_nat i)) by exact (te_more_lt regs rg mo 9 ltac:(lia)).
assert (A74 : ew E 74 = w64 (kid + 56 * Z.of_nat i)) by exact (te_more_lt regs rg mo 10 ltac:(lia)).
assert (A75 : ew E 75 = w64 nn) by exact (te_more_lt regs rg mo 11 ltac:(lia)).
assert (A76 : ew E 76 = w64 atv) by exact (te_more_lt regs rg mo 12 ltac:(lia)).
assert (U41 : bv_unsigned (ew E 41) = sp1v) by (rewrite A41; apply unsigned_lit_small; lia).
assert (U51 : bv_unsigned (ew E 51) = F) by (rewrite A51; apply unsigned_lit_small; lia).
assert (U53 : bv_unsigned (ew E 53) = Z.of_nat i) by (rewrite A53; apply unsigned_lit_small; lia).
assert (U56 : bv_unsigned (ew E 56) = 8 * Z.of_nat i) by (rewrite A56; apply unsigned_lit_small; lia).
assert (U58 : bv_unsigned (ew E 58) = 56 * Z.of_nat i) by (rewrite A58; apply unsigned_lit_small; lia).
assert (U59 : bv_unsigned (ew E 59) = SHADOW_OFF) by (rewrite A59; apply unsigned_lit_small; cbv [SHADOW_OFF]; lia).
assert (U64 : bv_unsigned (ew E 64) = doc') by (rewrite A64; apply unsigned_lit_small; lia).
assert (U65 : bv_unsigned (ew E 65) = kb) by (rewrite A65; apply unsigned_lit_small; lia).
assert (U66 : bv_unsigned (ew E 66) = kd) by (rewrite A66; apply unsigned_lit_small; lia).
assert (U67 : bv_unsigned (ew E 67) = kb + 8 * Z.of_nat i) by (rewrite A67; apply unsigned_lit_small; lia).
assert (U68 : bv_unsigned (ew E 68) = kd + 8 * Z.of_nat i) by (rewrite A68; apply unsigned_lit_small; lia).
assert (U69 : bv_unsigned (ew E 69) = xb) by (rewrite A69; apply unsigned_lit_small; lia).
assert (U70 : bv_unsigned (ew E 70) = xd) by (rewrite A70; apply unsigned_lit_small; lia).
assert (U71 : bv_unsigned (ew E 71) = kib) by (rewrite A71; apply unsigned_lit_small; lia).
assert (U72 : bv_unsigned (ew E 72) = kid) by (rewrite A72; apply unsigned_lit_small; lia).
assert (U73 : bv_unsigned (ew E 73) = kib + 56 * Z.of_nat i) by (rewrite A73; apply unsigned_lit_small; lia).
assert (U74 : bv_unsigned (ew E 74) = kid + 56 * Z.of_nat i) by (rewrite A74; apply unsigned_lit_small; lia).
assert (U75 : bv_unsigned (ew E 75) = nn) by (rewrite A75; apply unsigned_lit_small; lia).
assert (U76 : bv_unsigned (ew E 76) = atv) by (rewrite A76; apply unsigned_lit_small; lia).
(* an atom's U value *)
assert (UA : forall n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v).
{ intros n v H. rewrite ts_U0. exact H. }
assert (UO : forall n v c, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c).
{ intros n v c H Hc. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. }
split.
2:{ unfold sh_ok, ct6_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; unfold ct6_Bx; rewrite <- (aview_rd_of SEGS);
    rewrite (UA 59%nat SHADOW_OFF U59); rewrite ?Z.add_0_r, ?Z.sub_0_r, ?Z.max_r, ?Z.min_l by lia.
    - rewrite (UA 64%nat doc' U64). split; [exact RAd|].
      intros a Ha. destruct APd as (A1 & [A2 | (A3 & A4)]); cbv [kLowShadowBeg kHighMemBeg SHADOW_OFF] in *; lia.
    - rewrite (UA 67%nat _ U67). split; [exact RAkb|].
      intros a Ha. destruct APkb as (A1 & [A2 | (A3 & A4)]); cbv [kLowShadowBeg kHighMemBeg SHADOW_OFF] in *; lia.
    - rewrite (UA 68%nat _ U68). split; [exact RAkd|].
      intros a Ha. destruct APkd as (A1 & [A2 | (A3 & A4)]); cbv [kLowShadowBeg kHighMemBeg SHADOW_OFF] in *; lia. }
unfold ct6_ssx. apply ts_st_ok.
all: fold E.
- (* the registers: current, but x22 = shadow (&doc->keys) *)
  intros r. unfold ct6_regs. destruct (bv_eqb r 22%bv) eqn:Er.
  + apply bv_eqb_eq in Er. subst r. rewrite sr_get_set_same by reflexivity. rewrite R22. symmetry.
    apply (ct6_shx_denot E 64 32 doc' A64 A59); lia.
  + rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in Er; discriminate). apply te_regs_ok.
- vm_compute. reflexivity.
- unfold ct6_mem. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  + apply (ts_rok E _ 41 sp1v); [exact U41 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]].
    * apply (ts_chunk E _ sp1v 40 8 _ (shadow_addr (doc' + 24))); [| cbv [shadow_addr SHADOW_OFF]; lia | lia | exact C40].
      apply (ct6_shx_denot E 64 24 doc' A64 A59); lia.
    * apply (ts_chunk E _ sp1v 48 8 _ (doc' + 32)); [| lia | lia | exact C48].
      apply (ct6_denot_off E 64%nat 32 doc' A64); lia.
    * apply (ts_chunk E _ sp1v 56 8 _ (F + 32)); [| lia | lia | exact C56].
      apply (ct6_denot_off E 51%nat 32 F A51); lia.
    * apply (ts_chunk E _ sp1v 64 8 _ atv); [| lia | lia | exact C64].
      apply (ct6_denot_at E 76%nat atv A76); lia.
    * apply (ts_chunk E _ sp1v 72 8 _ (doc' + 24)); [| lia | lia | exact C72].
      apply (ct6_denot_off E 64%nat 24 doc' A64); lia.
    * apply (ts_chunk E _ sp1v 80 8 _ (shadow_addr (doc' + 40))); [| cbv [shadow_addr SHADOW_OFF]; lia | lia | exact C80].
      apply (ct6_shx_denot E 64 40 doc' A64 A59); lia.
    * apply (ts_chunk E _ sp1v 88 8 _ (doc' + 40)); [| lia | lia | exact C88].
      apply (ct6_denot_off E 64%nat 40 doc' A64); lia.
  + apply (ts_rok E _ 51 F); [exact U51 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor; [|constructor]].
    * apply (ts_chunk E _ F 56 8 _ kib); [| lia | lia | exact CB56].
      apply (ct6_denot_at E 71%nat kib A71); lia.
    * apply (ts_chunk E _ F 64 8 _ kb); [| lia | lia | exact CB64].
      apply (ct6_denot_at E 65%nat kb A65); lia.
  + apply (ts_rok E _ 64 doc'); [exact U64 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (ts_chunk E _ doc' 24 8 _ kid); [| lia | lia | exact CD24].
      apply (ct6_denot_at E 72%nat kid A72); lia.
    * apply (ts_chunk E _ doc' 32 8 _ kd); [| lia | lia | exact CD32].
      apply (ct6_denot_at E 66%nat kd A66); lia.
    * apply (ts_chunk E _ doc' 40 8 _ nn); [| lia | lia | exact CD40].
      apply (ct6_denot_at E 75%nat nn A75); lia.
  + apply (ts_rok E _ 67 (kb + 8 * Z.of_nat i)); [exact U67 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ (kb + 8 * Z.of_nat i) 0 8 _ xb); [| lia | lia | rewrite Z.add_0_r; exact CKB].
    apply (ct6_denot_at E 69%nat xb A69); lia.
  + apply (ts_rok E _ 68 (kd + 8 * Z.of_nat i)); [exact U68 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ (kd + 8 * Z.of_nat i) 0 8 _ xd); [| lia | lia | rewrite Z.add_0_r; exact CKD].
    apply (ct6_denot_at E 70%nat xd A70); lia.
- unfold ct6_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi ct6_s1 ct6_back ct6_doc ct6_kb ct6_kd]. rewrite !ts_bv_some.
  rewrite U41, U51, U64, U67, U68. repeat split; lia.
- split; [|split].
  + cbn [f_atoms]. apply ct6_atoms_app; [exact XA|]. clearbody E mo. unfold ct6_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U59, U41, U51, U53, U56, U58, U64, U65, U66, U67, U68, U69, U70, U71, U72, U73, U74, U75, U76.
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
    rewrite !Z.mod_1_r. cbv [SHADOW_OFF]. lia.
  + cbn [f_conds]. apply ct6_conds_app; [exact XC|]. clearbody E mo. unfold ct6_conds. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ltu_U, !branch_geu_U.
    rewrite (UA 53%nat _ U53), (UA 75%nat _ U75), (UA 67%nat _ U67), (UA 65%nat _ U65), (UA 68%nat _ U68), (UA 66%nat _ U66),
      (UA 73%nat _ U73), (UA 71%nat _ U71), (UA 74%nat _ U74), (UA 72%nat _ U72).
    repeat split; first [apply Z.ltb_lt; lia | apply negb_true_iff, Z.ltb_ge; lia].
  + cbn [f_alias]. clearbody E mo. unfold ct6_alias. cbn [alias_ok].
    repeat split; apply U_inj; rewrite ?U_SAlu, ?U_SMd, ?U_SLit;
      rewrite ?(UA 65%nat _ U65), ?(UA 66%nat _ U66), ?(UA 67%nat _ U67), ?(UA 68%nat _ U68), ?(UA 71%nat _ U71), ?(UA 72%nat _ U72),
        ?(UA 73%nat _ U73), ?(UA 74%nat _ U74), ?(UA 53%nat _ U53), ?(UA 56%nat _ U56), ?(UA 58%nat _ U58);
      unfold zcanon, M64, zalu_raw, zmd_raw.
    * rewrite (Z.mod_small (kb + 8 * Z.of_nat i)) by lia. reflexivity.
    * rewrite (Z.mod_small (kd + 8 * Z.of_nat i)) by lia. reflexivity.
    * rewrite (Z.mod_small (kib + 56 * Z.of_nat i)) by lia. reflexivity.
    * rewrite (Z.mod_small (kid + 56 * Z.of_nat i)) by lia. reflexivity.
    * rewrite !(Z.mod_small 6), !(Z.mod_small 3) by lia. change (Z.land 6 63) with 6. change (Z.land 3 63) with 3.
      rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
      rewrite !(Z.mod_small (Z.of_nat i * 64)), !(Z.mod_small (Z.of_nat i * 8)) by lia.
      rewrite Z.mod_small by lia. lia.
    * rewrite (Z.mod_small 60) by lia. change (Z.land 60 63) with 60. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_small by lia. reflexivity.
    * rewrite (Z.mod_small 63) by lia. change (Z.land 63 63) with 63. rewrite Z.shiftr_div_pow2 by lia.
      rewrite ct6_swrap_small by lia. rewrite Z.div_small by lia. reflexivity.
    * rewrite (Z.mod_small 56) by lia.
      rewrite !ct6_swrap_small by lia. change (Z.of_N 64) with 64.
      rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.


Lemma ct6_nodup_fst : forall (l : list (Z * Z)) k a b, NoDup (map fst l) -> In (k, a) l -> In (k, b) l -> a = b.
Proof.
induction l as [|[k0 v0] l IH]; intros k a b Hnd Ha Hb; [destruct Ha|].
cbn [map fst] in Hnd. apply list_relations.list.NoDup_cons in Hnd as [Hni Hnd'].
destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
- injection Ea as E1 E2. injection Eb as E3 E4. congruence.
- injection Ea as <- <-. exfalso. apply Hni. apply list_elem_of_In. exact (in_map fst _ (k0, b) Hb).
- injection Eb as <- <-. exfalso. apply Hni. apply list_elem_of_In. exact (in_map fst _ (k0, a) Ha).
- exact (IH k a b Hnd' Ha Hb).
Qed.

(* ---- the entry of every stretch: the L3 facts give the symbolic state at any of the three cuts, and the member's
   facts (key strings, value nodes, the blocks they lie in) at the current memory ---- *)
Lemma ct6_entry : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i pc,
  L3B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i ->
  exists kb kd xb xd kib kid capb capd nm u u' kxb kxd Db1 Dd1,
    nth_error ms i = Some (nm, u) /\
    nth_error (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)) i = Some (nm, u') /\
    pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) xb kxb nm /\
    pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) xd kxd nm /\
    pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (kib + 56 * Z.of_nat i) u' Db1 /\
    pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (kid + 56 * Z.of_nat i) u Dd1 /\
    In (kib, 56 * capb) Lamc /\ In (kid, 56 * capd) Lamc /\ Z.of_nat i < capb /\ Z.of_nat i < capd /\
    incl Db1 Lamc /\ incl Dd1 Lamc /\ Z.of_nat (length ms) <= 2 ^ 44 /\
    sh_ok SEGS ct6_Bx ct6_SH
      (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i))
      (mrestrict (w_H Wc) memc) /\
    (forall xa xc,
      atoms_ok (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)) xa ->
      conds_ok (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)) xc ->
      st_ok_pi SEGS VAL (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i))
        (ct6_ssx pc xa xc) (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS)))).
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i pc HL3.
pose proof (crt_at_L3_B_obj HL3) as Ht. pose proof (crt_at_L3_B_frm_zero HL3) as HFZ.
pose proof (crt_at_L3_B_fregs HL3) as HFK. pose proof (crt_at_L3_B_live HL3) as HL.
pose proof (crt_at_L3_B_bregs HL3) as HBR. pose proof (crt_at_L3_B_s5_i HL3) as R21.
pose proof (crt_at_L3_B_s8_i HL3) as R24. pose proof (crt_at_L3_B_s10_i HL3) as R26.
pose proof (crt_at_L3_B_s6_keys HL3) as R22. pose proof (crt_at_L3_B_sp_saved HL3) as SPsv.
pose proof (crt_at_L3_B_sp_shkids HL3) as SPshk. pose proof (crt_at_L3_B_sp_keys HL3) as SPkeys.
pose proof (crt_at_L3_B_sp_back HL3) as SPback. pose proof (crt_at_L3_B_sp_at HL3) as SPat.
pose proof (crt_at_L3_B_sp_kids HL3) as SPkids. pose proof (crt_at_L3_B_sp_shn HL3) as SPshn.
pose proof (crt_at_L3_B_sp_pn HL3) as SPpn. pose proof (crt_at_L3_B_doc_align HL3) as Hd8.
pose proof (crt_at_L3_B_doc_open HL3) as RAd. pose proof (crt_at_L3_B_back_open HL3) as RAb.
pose proof (crt_at_L3_B_v_open HL3) as RAv. pose proof (crt_at_L3_B_i_lt HL3) as Hi.
pose proof (crt_at_L3_B_cset_range HL3) as Hcs1. pose proof (crt_at_L3_B_cset_mod HL3) as Hcs2.
pose proof (crt_at_L3_B_cnt HL3) as Hcnt. pose proof (crt_at_L3_B_saved_nz HL3) as Hsv.
pose proof (crt_at_L3_B_copy HL3) as HTC. pose proof (crt_at_L3_B_copy_fd HL3) as HFD.
pose proof (crt_at_L3_B_back HL3) as HBK. pose proof (crt_at_L3_B_pos HL3) as HPOS. clear HL3.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNl.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL. clear HSD.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3. pose proof (crt_bregs_B_tp HBR) as R4.
pose proof (crt_bregs_B_s0 HBR) as R8. pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19. pose proof (crt_bregs_B_s7 HBR) as R23.
pose proof (crt_bregs_B_s9 HBR) as R25. pose proof (crt_bregs_B_s11 HBR) as R27.
pose proof (proj1 HJ) as HAR.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hd1 & Hd2 & Hd3 & Hd4).
pose proof (YM05.alloc_ceiling_val) as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr lyc CRT_CID pos) in *.
set (m := mrestrict (w_H Wc) memc) in *.
assert (Hl0 : (0 < length ms)%nat) by lia.
(* the document's header *)
rewrite Ht in HDOC.
destruct (ct6_obj_hdr SEGS m (prh_lin Lamc) doc ms D HDOC Hl0)
  as (kid & kd & capd & Ddi & Cd24 & Cd32 & Cd40 & _ & Hncd & Lkid & Lkd & EDd & NDd & Hmd).
(* the read-back's header: the rewritten tree pj_set_model ms ck_MOD_AT STAMP *)
unfold crt_tc in HBK. rewrite Ht, cm_crt_tree_obj in HBK.
set (ms' := PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)) in *.
assert (Hlen' : (length ms <= length ms')%nat) by (unfold ms'; rewrite cm_set_len; destruct (Nat.eqb _ _); lia).
destruct (ct6_obj_hdr SEGS m (prh_lin Lamc) (F + CRT_OFF_BACK) ms' Dback HBK ltac:(lia))
  as (kib & kb & capb & Dbi & Cb24 & Cb32 & Cb40 & _ & Hncb & Lkib & Lkb & EDb & NDb & Hmb).
(* member i *)
destruct (nth_error ms i) as [[nm u]|] eqn:Enth; [|apply nth_error_None in Enth; lia].
destruct (cm_set_member ms (PjTree.JStr ck_STAMP) i nm u Enth) as (u' & Enth' & _ & _). fold ms' in Enth'.
destruct (ct6_mems_nth SEGS m (prh_lin Lamc) _ ms kid kd Ddi i nm u Hmd Enth)
  as (xd & kxd & Dd1 & Cxd & Hcd & Hnd & Hind & Hincd).
destruct (ct6_mems_nth SEGS m (prh_lin Lamc) _ ms' kib kb Dbi i nm u' Hmb Enth')
  as (xb & kxb & Db1 & Cxb & Hcb & Hnb & Hinb & Hincb).
(* the blocks *)
unfold prh_lin in Lkid, Lkd, Lkib, Lkb.
destruct (ct6_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 kd (8 * capd) HAR HLED Lkd)
  as (kd0 & kd16 & kd4 & kdc & kdapp & kdab & kdra & _ & _).
destruct (ct6_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 kb (8 * capb) HAR HLED Lkb)
  as (kb0 & kb16 & kb4 & kbc & kbapp & kbab & kbra & _ & _).
destruct (ct6_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 kid (56 * capd) HAR HLED Lkid)
  as (kid0 & kid16 & kid4 & kidc & _ & _ & _ & _ & _).
destruct (ct6_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 kib (56 * capb) HAR HLED Lkib)
  as (kib0 & kib16 & kib4 & kibc & _ & _ & _ & _ & _).
pose proof Hcd as (Lxd & Hxd1 & _ & _). pose proof Hcb as (Lxb & Hxb1 & _ & _). unfold prh_lin in Lxd, Lxb.
destruct (ct6_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 xd kxd HAR HLED Lxd) as (xd0 & xd16 & xd4 & xdc & _).
destruct (ct6_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 xb kxb HAR HLED Lxb) as (xb0 & xb16 & xb4 & xbc & _).
(* the blocks the walk holds are apart from the document's; the frames and blocks are pairwise apart *)
assert (HDb : forall bk, In bk Dback -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. left. exact Hbk. }
assert (Hkbkd : kb <> kd).
{ intros Ekk. subst kd.
  assert (Ecap : 8 * capb = 8 * capd).
  { destruct HLED as (_ & HND & _). exact (ct6_nodup_fst Lamc kb _ _ HND Lkb Lkd). }
  apply (HAP (kb, 8 * capb)).
  - apply in_or_app. left. rewrite EDb. right. left. reflexivity.
  - rewrite Ecap, EDd. right. left. reflexivity. }
destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as (Hsep & _).
destruct (pairwise_app_inv _ _ _ Hsep) as (Hpb & Hpf & Hbf).
pose proof HJ as (_ & Hly & _ & _ & _ & HFR & _).
pose proof (cb4_ar0 B ARx ly S Hp W regs mem md ch HPRE) as HAR0.
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc HAR0 Hly) as (_ & Efa & _).
pose proof HTREE as (_ & _ & _ & (_ & (cid' & pos' & Hin' & Hdf1 & Hdf2) & _)).
rewrite <- (Efa cid' pos') in Hdf1, Hdf2.
assert (Hfr' : In (cid', pos') (frames Sc)) by (rewrite HFR; right; exact Hin').
set (brng := fun b : Z * Z => (fst b, req_size (snd b))) in *.
set (frng := fun f : Z * Z => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) in *.
assert (Hrq : forall k, 0 <= k -> req_size (k + 16) = k + 16) by (intros k Hk; unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
assert (Zfd : zdisjoint (F, 512) (frame_addr lyc cid' pos', fs_frame_bytes cid')).
{ rewrite HFR in Hpf. cbn [map app] in Hpf. destruct Hpf as (Hf0 & _).
  pose proof (proj1 (Forall_forall _ _) Hf0 (frng (cid', pos')) (in_map frng _ _ Hin')) as Z0.
  unfold frng in Z0. cbn [fst snd] in Z0. rewrite cb4_fb in Z0. exact Z0. }
assert (Zbf : forall a k, In (a - 16, k + 16) (ablocks B lyc Sc) -> 0 <= k ->
  zdisjoint (a - 16, k + 16) (F, 512) /\ zdisjoint (a - 16, k + 16) (frame_addr lyc cid' pos', fs_frame_bytes cid')).
{ intros a k Hab Hk.
  pose proof (in_map brng _ _ Hab) as Hb. unfold brng in Hb. cbn [fst snd] in Hb. rewrite (Hrq k Hk) in Hb.
  split.
  - pose proof (Hbf _ _ Hb (in_map frng _ _ Hin)) as Z0. unfold frng in Z0. cbn [fst snd] in Z0. rewrite cb4_fb in Z0. exact Z0.
  - exact (Hbf _ _ Hb (in_map frng _ _ Hfr')). }
assert (Zbb : zdisjoint (kb - 16, 8 * capb + 16) (kd - 16, 8 * capd + 16)
           \/ zdisjoint (kd - 16, 8 * capd + 16) (kb - 16, 8 * capb + 16)).
{ pose proof (in_map brng _ _ kbab) as Hb1. pose proof (in_map brng _ _ kdab) as Hb2.
  unfold brng in Hb1, Hb2. cbn [fst snd] in Hb1, Hb2.
  rewrite (Hrq (8 * capb) ltac:(lia)) in Hb1. rewrite (Hrq (8 * capd) ltac:(lia)) in Hb2.
  apply (ct6_pairwise_neq _ _ _ _ Hpb Hb1 Hb2). intros E0. injection E0 as E1 _. lia. }
destruct (Zbf kb (8 * capb) kbab ltac:(lia)) as (Zb1 & Zb2).
destruct (Zbf kd (8 * capd) kdab ltac:(lia)) as (Zd1 & Zd2).
unfold zdisjoint in Zfd, Zb1, Zb2, Zd1, Zd2, Zbb. cbn [fst snd] in Zfd, Zb1, Zb2, Zd1, Zd2, Zbb.
assert (Hfsp : 0 < fs_frame_bytes cid') by (pose proof (fs_frame_bytes_nonneg cid'); lia).
pose proof Hd8 as Hd8'.
exists kb, kd, xb, xd, kib, kid, capb, capd, nm, u, u', kxb, kxd, Db1, Dd1.
split; [first [exact Enth | reflexivity]|]. split; [exact Enth'|]. split; [exact Hcb|]. split; [exact Hcd|].
split; [exact Hnb|]. split; [exact Hnd|]. split; [exact Lkib|]. split; [exact Lkid|].
assert (Hlm : (length ms <= Z.to_nat capd)%nat) by lia.
split; [lia|]. split; [lia|].
split; [intros bk Hbk; apply HDb; rewrite EDb; right; right; apply Hincb; exact Hbk|].
split; [intros bk Hbk; apply HDL; rewrite EDd; right; right; apply Hincd; exact Hbk|].
split; [lia|].
pose proof (cm_at_le ms) as Hatl.
destruct Cd24 as (_ & Cd24). destruct Cd32 as (_ & Cd32). destruct Cd40 as (_ & Cd40).
destruct Cb24 as (_ & Cb24). destruct Cb32 as (_ & Cb32). destruct Cxd as (Rxd & Cxd). destruct Cxb as (Rxb & Cxb).
cut (forall xa xc,
  atoms_ok (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)) xa ->
  conds_ok (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)) xc ->
  st_ok_pi SEGS VAL (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i))
    (ct6_ssx pc xa xc) (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS ct6_Bx ct6_SH
    (TEB regs rg (ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i))
    (mrestrict (w_H Wc) memc)).
{ intros HX. split; [exact (proj2 (HX [] [] I I))|]. intros xa xc XA XC. exact (proj1 (HX xa xc XA XC)). }
intros xa xc XA XC.
apply (ct6_st_ok fxk pc Wc memc rg sp1 F doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms))
  capb capd i); try assumption.
all: try lia.
all: try (unfold CRT_OFF_BACK in *; lia).
all: try exact SPshk. all: try exact SPkeys. all: try exact SPback. all: try exact SPat. all: try exact SPkids.
all: try exact SPshn. all: try exact SPpn. all: try exact Hd3.
all: try (replace (F + 56) with (F + CRT_OFF_BACK + 24) by (unfold CRT_OFF_BACK; lia); exact Cb24).
all: try (replace (F + 64) with (F + CRT_OFF_BACK + 32) by (unfold CRT_OFF_BACK; lia); exact Cb32).
all: try (apply kbra; lia). all: try (apply kdra; lia).
all: try (apply (in_app_sub _ _ _ _ kbapp); lia). all: try (apply (in_app_sub _ _ _ _ kdapp); lia).
Qed.

End g.
End f.
End t6.
