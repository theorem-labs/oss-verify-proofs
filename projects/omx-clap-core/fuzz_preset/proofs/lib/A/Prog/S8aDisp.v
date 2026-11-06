(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_identity_poll_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlIdentityPollBlock.v, with its module paths, module names and numbers changed; 695 of its 772 lines of code are new or changed and 346 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/FuzzStrdup.v, with its module names changed; 1135 of its 1207 lines of code are new or changed and 700 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d / unstripped twin bff8519b): pieces 2 + 3 + 4 of the walk
   of ex_value (A' 0x832a4) against the text tex_value_specX (lib/A/PRH_FnEx.v), the statement ev_disp_spec of
   lib/A/Prog/S8aIface.v: from P_WS (0x833dc) through the inlined ex_ws, the end test and the switch on the byte (piece 2),
   the string arm (piece 3: ex_string, v->type, strcmp, in->differs) and the word arms (piece 4: ex_word on "true" /
   "false" / "null"), to P_KIND at 0x834bc ('{' / '[') or 0x83568 (a number's byte), or to P_EXIT (0x83d48).
   Engine: YC1fPx / YC80x over YCbqG's ajournal_x (generic over ARx); calls through YCbqGcall's aj_call_xWF (ex_string,
   ex_word: their caller-window fpostW posts, lifted to the float form with fx' = fx) and YGcallMx's aj_strcmp_at_x.
   Numerals: EV_* offsets and 0x158 / 0x1a4 (LENGTH: pc - 0x832a4 on the bff8519b listing); 272, 256, 152, 112, 120
   (LENGTH: ex_value's frame per nesting at prh_img_A, its `addi sp, sp, -256`, the save area's lowest slot, the spill
   slot s1 + 112); 16384, 4096, 8192 (LENGTH: STK_RT_STRTOD, ESTACK, 2 * ESTACK); 8, 16, 32, 40, 56, 128 (LENGTH: word,
   granule / alignment, struct ex size, a tree node, the class-1 fake frame); atom indices 2-34 (DERIVED: Ereg's
   register and extra atoms); 2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 64 (DERIVED: shadow, stack and word bounds); 34, 91, 93,
   102, 109, 110, 116, 123 (WORD: the bytes quote, '[', ']', 'f', 'm', 'n', 't', '{' the switch compares). No ADDRESS
   literal: addresses come from pa_sigma / pa_val of PAImg_prog.v and the PrhImg fields of PRH_Img.v.
   MEMNORM (S8aIface.v ev_mid's last conjunct, walkkit old-pin 4951e104ca2e): every runner segment keeps
   `YAkMemnorm.memnorm SEGS mem` by YC1fPx's `*_inv` runners (paj_run_x_inv / paj_run_to_x_inv at P := that predicate,
   laws YSRrMemnorm.srr_inv_laws_memnorm_k); ev_mid_frame takes it at the new memory. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallMx YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* plain lia: the imported `lia` prunes hypotheses (Lib/LiaTwx2.v) and fails on goals over record projections *)
Ltac zl := Zify.zify; xlia zchecker.

(* ---- the cut points internal to piece 2 (LENGTH, offsets from ex_value's entry) ---- *)
Definition EV_LP : Z := 0x158.   (* 0x833fc: the first slot of the inlined ex_ws loop *)
Definition EV_TL : Z := 0x1a4.   (* 0x83448: after the loop: the end test and the switch *)
(* ex_value's entry as a listing offset (DERIVED: the generated A_prog_sigma / A_prog_base) *)
Definition EV0 : Z := A_prog_sigma AS_ex_value - A_prog_base.

Lemma ev_mod32 : forall sp0, sp0 mod 16 = 0 ->
  (sp0 - 256 - (sp0 - 256) mod 32) mod 32 = 0 /\
  sp0 - 272 <= sp0 - 256 - (sp0 - 256) mod 32 <= sp0 - 256.
Proof.
intros sp0 H. pose proof (Z.div_mod (sp0 - 256) 32 ltac:(zl)) as D. pose proof (Z.mod_pos_bound (sp0 - 256) 32 ltac:(zl)) as M.
pose proof (Z.div_mod sp0 16 ltac:(zl)) as D16.
replace (sp0 - 256 - (sp0 - 256) mod 32) with (32 * ((sp0 - 256) / 32)) by zl.
rewrite Z.mul_comm, Z.mod_mul by zl. split; [reflexivity|]. zl.
Qed.

(* ---- pure, the tree's footprint blocks satisfy lblk: COPIED from preset's released plain lib/Prog/pj_get.v:75-121
   (gp_items_blocks / gp_mems_blocks / gp_node_blocks; tree predicates only, no machine state), restated over any
   segment list and over PRH_Reader's pj_itemsR / pj_memsR / pj_nodeR (the kit's tree representation since walkkit
   b77223726823, prhex_tree) ---- *)
Lemma ev_items_blocks : forall (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  (forall a' u D1, In u l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  PRH_Reader.pj_itemsR P a l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros lblk P l. induction l as [|u l IH]; intros a D HP H x k Hin; cbn [PRH_Reader.pj_itemsR] in H.
  - subst D. destruct Hin.
  - destruct H as (D1 & D2 & -> & HPu & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (HP a u D1 (or_introl eq_refl) HPu x k Hin).
    + apply (IH (a + 56) D2); [|exact Hr|exact Hin]. intros a' u' D1' Hu. apply HP. right. exact Hu.
Qed.
Lemma ev_mems_blocks : forall segs m (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall a' nm u D1, In (nm, u) l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  PRH_Reader.pj_memsR segs m lblk P a ka l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros segs m lblk P l. induction l as [|[nm u] l IH]; intros a ka D HP H x k Hin; cbn [PRH_Reader.pj_memsR] in H.
  - subst D. destruct Hin.
  - destruct H as (x0 & k0 & D1 & D2 & -> & _ & (Hl & _) & HPu & Hr).
    destruct Hin as [E|Hin]; [injection E as <- <-; exact Hl|].
    apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (HP a nm u D1 (or_introl eq_refl) HPu x k Hin).
    + apply (IH (a + 56) (ka + 8) D2); [|exact Hr|exact Hin]. intros a' nm' u' D1' Hu. apply (HP a' nm' u' D1'). right. exact Hu.
Qed.
Lemma ev_node_blocks : forall segs t m lblk p D, PRH_Reader.pj_nodeR segs m lblk p t D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros segs t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H x k Hin;
    cbn [PRH_Reader.pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & H).
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
  - destruct H as (_ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
  - destruct H as (_ & _ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
      destruct Hin as [E|[]]. injection E as <- <-. destruct Hc as [(C1 & _)|(_ & Hl)]; [lia | exact Hl].
    + rewrite Forall_forall in IH.
      apply (ev_items_blocks lblk (PRH_Reader.pj_nodeR segs m lblk) items kids Di); [|exact Hi | exact Hin].
      intros a' u D1 Hu H1. exact (IH u Hu m lblk a' D1 H1).
  - destruct H as (_ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
      destruct Hc as [(C1 & _)|(_ & Hl1 & Hl2)]; [lia|].
      destruct Hin as [E|[E|[]]]; injection E as <- <-; assumption.
    + rewrite Forall_forall in IH.
      apply (ev_mems_blocks segs m lblk (PRH_Reader.pj_nodeR segs m lblk) members kids keys Di); [|exact Hi | exact Hin].
      intros a' nm u D1 Hu H1. exact (IH (nm, u) Hu m lblk a' D1 H1).
Qed.

(* ---- the symbolic states of piece 2 (closed terms: the engine vm_computes from them) ---- *)
Definition D_Bx : sv := SOff 24 0.
Definition D_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* P_WS: in->p = atom 32, in->end = atom 33; in at s3 (atom 19), its shadow byte at s10 (atom 26) *)
Definition ss_ws : sstate :=
  mkSS (EV0 + EV_WS) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ]
    None (mkFacts [] [] []).

Lemma ev_denot_atom : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ev_vm1_of_aview : forall segs (H : word -> bool) mem z, aview segs H mem z = Some 0 -> val_mem segs (mrestrict H mem) z 1 0.
Proof.
intros segs H mem z E k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in E. destruct (mbyte segs (mrestrict H mem) z) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma ev_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Hr). rewrite forallb_forall in Hro.
specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma ev_vm_eq : forall segs (m m' : word -> option byte) a n v, (forall x, m' x = m x) -> val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros segs m m' a n v H Hv k Hk. unfold mbyte. rewrite H. exact (Hv k Hk). Qed.

(* 0x83448 at the end of the text: in->p = in->end = a2 (atom 12) *)
Definition ss_te : sstate :=
  mkSS (EV0 + EV_TL) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 12 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ]
    None (mkFacts [] [] []).
(* 0x83448 before a byte: in->p = atom 32, the byte = atom 33, in->end = a2 (atom 12); the spill slot s1 + 112 *)
Definition D_QLO : Z := 0x7fff7f800000.
Definition ss_tb : sstate :=
  mkSS (EV0 + EV_TL) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
      YP09.mkRegion (Some 9%nat) 112 120 112 120 [];
      YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ]
    None (mkFacts [ (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (9%nat, mkAF D_QLO (2 ^ 47) 5);
                    (32%nat, mkAF 4096 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0); (12%nat, mkAF 4096 (2 ^ 47) 0) ] [] []).
Definition SH_tb : list shent := [mkSHE 32 0 1].

Lemma ev_blt_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned. fold (U E a). fold (U E b).
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 64) with (2 ^ 63) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite !Z.mod_small by zl.
replace (U E a + 2 ^ 63 - 2 ^ 63) with (U E a) by zl. replace (U E b + 2 ^ 63 - 2 ^ 63) with (U E b) by zl. reflexivity.
Qed.
Lemma ev_skipn_cons : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
intros x. induction x as [|b x IH]; intros i Hi; [cbn in Hi; lia|]. destruct i as [|i]; [reflexivity|].
cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.
Lemma ev_frame_slot : forall E rs (m m' : word -> option byte) lo hi, frame_of E rs m m' ->
  (forall z, in_wrange E rs z -> lo <= z < hi) -> forall x, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.
Proof. intros E rs m m' lo hi HF Hw x Hx. apply HF. intros H. exact (Hx (Hw _ H)). Qed.
Ltac uat n v Hn H :=
  match type of H with context [U ?E' (SOff n 0)] =>
    let Hx := fresh "Hx" in assert (Hx : ew E' n = w64 v) by (cbn [ew ewset Nat.eqb]; exact Hn);
    rewrite (U_atom E' n v Hx) in H by zl; clear Hx end.

Lemma ev_blt_lit : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit z)) (sv_denot E (SOff n 0)) = (z <? v).
Proof.
intros E n v z H Hv Hz. rewrite ev_blt_U; rewrite ?U_SLit, ?(U_atom E n v H) by zl; rewrite ?zcanon_id by (unfold M64; zl);
  [reflexivity | zl | zl].
Qed.
Lemma ev_beq_lit : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v =? z).
Proof. intros E n v z H Hv Hz. rewrite branch_eq_U, U_SLit, (U_atom E n v H) by zl. rewrite zcanon_id by (unfold M64; zl). reflexivity. Qed.
Lemma ev_bne_lit : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = negb (v =? z).
Proof. intros E n v z H Hv Hz. rewrite branch_ne_U, U_SLit, (U_atom E n v H) by zl. rewrite zcanon_id by (unfold M64; zl). reflexivity. Qed.

Lemma ev_chunk8_val : forall segs E (m : word -> option byte) base off e v,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem segs m (base + off) 8 v.
Proof.
intros segs E m base off e v HC He Hv k Hk. destruct (HC (Z.of_nat k) ltac:(cbn; zl)) as (b & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite He in Hb. injection Hb as <-. rewrite Hm. f_equal.
apply bv_eq. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64). change (8 * Z.of_nat 8) with 64.
rewrite (Z.mod_small v (2 ^ 64)) by zl. rewrite Z.mod_mod by zl. reflexivity.
Qed.
(* the loop head 0x833fc: a0 = a1 = in->p (atom 32), a3 = 32, a4 = the mask; in at s3 with in->p in it (writable), the
   shadow byte of in at s10, the byte at in->p (atom 33) *)
Definition ss_lp : sstate :=
  mkSS (EV0 + EV_LP)
    (sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 32 0)) 11%bv (SOff 32 0)) 13%bv (SLit 32)) 14%bv (SLit EV_WSMASK))
    [ YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
      YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ]
    None (mkFacts [ (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF D_QLO (2 ^ 47) 3);
                    (32%nat, mkAF 4096 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0); (12%nat, mkAF 4096 (2 ^ 47) 0) ] [] []).

Lemma ev_mask_br : forall E n c, ew E n = w64 c -> 0 <= c <= 32 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff n 0)) (SLit 1))) (sv_denot E (SLit 0)) =
  negb (PjGrammar.ws c).
Proof.
intros E n c H Hc. rewrite branch_eq_U, U_SAlu, U_SAlu, !U_SLit, (U_atom E n c H) by zl.
assert (Hj : exists j : nat, (j <= 32)%nat /\ c = Z.of_nat j) by (exists (Z.to_nat c); split; zl).
destruct Hj as (j & Hj & ->). clear H Hc.
do 33 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma ev_denot_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv Hvc. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Ltac lp_inp HS E19 Ev :=
  let HMO := fresh "HMO" in let HRO := fresh "HRO" in let HCK := fresh "HCK" in
  pose proof (st_ok_mem_ok _ _ _ _ HS) as HMO; destruct HMO as (_ & HRO & _);
  cbn [ss_mem abs_ss add_cond setpc ms_mem restrict] in HRO;
  apply Forall_inv in HRO; destruct HRO as (_ & _ & _ & HCK); cbn [YP09.r_chunks YP09.r_base base_val] in HCK;
  apply Forall_inv in HCK;
  let Hx := fresh "Hx" in
  match type of HCK with YP09.chunk_ok _ ?Ex _ _ _ =>
    assert (Hx : ew Ex 19 = ew _ 19) by (cbn [ew ewset Nat.eqb]; reflexivity) end;
  rewrite Hx, E19 in HCK; clear Hx; unfold w64 in HCK; rewrite unsigned_lit_small in HCK by zl;
  pose proof (ev_chunk8_val _ _ _ _ _ _ _ HCK ltac:(apply ev_denot_off; [cbn [ew ewset Nat.eqb]; exact Ev | zl | zl]) ltac:(zl)) as Hp';
  rewrite Z.add_0_r in Hp'; clear HCK.

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Notation PIA := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation PL := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PIA)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS; hl, since HL clashes with proof names *)
Context {RL : PrhRoomLive}.  (* ev_mid's last conjunct (room_live_cf); S8aIface's Section c context *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* STAND-IN: NewFnWalks / h-hpreset-7, lands as YCbqG's alx_zshadow_byte (walks-new b092d73a858): the real stack's
   shadow bytes read 0 under ARx (the per-byte form of alx_zshadow) *)
Hypothesis ZSB_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
  aview SEGS (w_H W) mem (SHADOW_OFF + a / 8) = Some 0.

#[local] Notation PRE := (ev_pre (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx).
#[local] Notation MID := (ev_mid (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation REGS := (ev_regs (L := A_prog_listing) (PA := PA)).
#[local] Notation AT_WS := (ev_at_ws (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_KIND := (ev_at_kind (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_EXIT := (ev_at_exit (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation TO_EXIT := (ev_to_exit (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation CFG := (ev_cfg (L := A_prog_listing) (PA := PA)).
#[local] Notation FXOK := (ev_fx (fx := fx)).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation STKa a := (ea_STK (PI := PIA) (L := A_prog_listing) (PA := PA) a).
#[local] Notation sp0a a := (ea_sp0 (L := A_prog_listing) (PA := PA) a).
#[local] Notation S1a a := (ea_S1 (L := A_prog_listing) (PA := PA) a).
#[local] Notation SAa a := (ea_SA (L := A_prog_listing) (PA := PA) a).
#[local] Notation fra a := (ea_fr (L := A_prog_listing) (PA := PA) a).
#[local] Notation FPa a := (ea_FP (L := A_prog_listing) (PA := PA) a).
#[local] Notation lena a := (ea_len (L := A_prog_listing) (PA := PA) a).

(* ---- arithmetic of an activation (ev_pre) ---- *)
Lemma ev_arith : forall a, PRE a ->
  sp0a a mod 16 = 0 /\ YM05.alloc_ceiling <= ly_stk_lo (ea_ly a) /\ ly_stk_lo (ea_ly a) + STKa a <= sp0a a /\
  sp0a a + ea_d a <= ly_top (ea_ly a) /\ ly_top (ea_ly a) <= ly_stk_hi (ea_ly a) /\ ly_stk_hi (ea_ly a) <= 2 ^ 47 /\
  0 <= ea_d a /\ ea_d a mod 16 = 0 /\ sp0a a <= ea_q a /\ ea_q a + 40 <= sp0a a + ea_d a /\ ea_q a mod 8 = 0 /\
  STKa a = Z.of_nat (S (ea_n a)) * 272 + 16384 /\
  S1a a mod 32 = 0 /\ sp0a a - 272 <= S1a a <= sp0a a - 256 /\ SAa a = sp0a a - 256 /\
  4096 <= ea_x0 a /\ ea_x0 a + lena a <= YM05.alloc_ceiling /\ 0 <= ea_i0 a <= lena a /\ lena a <= 3 * 2 ^ 20 /\
  0 <= ea_dep a <= 32 /\ (ea_dl a = 0 \/ ea_dl a = 1).
Proof.
intros a HP. unfold ev_pre in HP. cbv zeta in HP.
destruct HP as ((HAF & HROD) & Hfrm & Hcnt & H10 & H11 & Hcur & Hqm & HCH & Hspq & Hq40 & Hfw & Hsrc & Hinb & Hlen & Hi0 &
  Hdep & Hdn & Hdl & Hwd & Hinbs & Hd1 & Hd2 & Htree & Hled).
destruct HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct Hfw as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct Hsrc as (_ & Hx4096 & Hxc & _).
assert (EK : STKa a = Z.of_nat (S (ea_n a)) * 272 + 16384).
{ unfold ea_STK, STK_ex_value. replace (zmaxl _) with 16384 by (vm_compute; reflexivity). reflexivity. }
pose proof (ev_mod32 (sp0a a) Hal16) as [M1 M2].
unfold ea_S1, ea_SA in *. unfold ea_sp0, ea_len in *.
repeat split; try zl.
Qed.

(* ---- the bytes ex_value's own straight-line code writes in pieces 2-4: its frame below the save area, in->p and
   in->differs ---- *)
Definition ev_wr (a : ev_act) (z : Z) : Prop :=
  (sp0a a - STKa a <= z < SAa a + 152) \/ (ea_q a <= z < ea_q a + 8) \/ (ea_q a + 32 <= z < ea_q a + 36).

Lemma ev_wr_ceil : forall a z, PRE a -> z < YM05.alloc_ceiling -> ~ ev_wr a z.
Proof.
intros a z HP Hz. pose proof (ev_arith a HP) as (_ & Hceil & Hslo & _ & _ & _ & _ & _ & Hspq & _ & _ & EK & _).
unfold ev_wr. intros [Hw|[Hw|Hw]]; zl.
Qed.
Lemma ev_wr_win : forall a z, PRE a -> sp0a a <= z < sp0a a + ea_d a -> ~ inFP (FPa a) z -> ~ ev_wr a z.
Proof.
intros a z HP Hz Hn Hw. pose proof (ev_arith a HP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESA & _).
apply Hn. unfold ea_FP. rewrite !inFP_cons. unfold ev_wr in Hw. destruct Hw as [Hw|[Hw|Hw]]; [zl | right; left; zl | right; right; right; left; zl].
Qed.
Lemma ev_wr_cur : forall a z, PRE a -> ea_q a + 8 <= z < ea_q a + 32 -> ~ ev_wr a z.
Proof.
intros a z HP Hz. pose proof (ev_arith a HP) as (_ & _ & _ & _ & _ & _ & _ & _ & Hspq & _ & _ & _ & _ & _ & ESA & _).
unfold ev_wr. intros [Hw|[Hw|Hw]];  zl.
Qed.
Lemma ev_wr_saved : forall a z, PRE a -> SAa a + 152 <= z < sp0a a -> ~ ev_wr a z.
Proof.
intros a z HP Hz. pose proof (ev_arith a HP) as (_ & _ & _ & _ & _ & _ & _ & _ & Hspq & _ & _ & _ & _ & _ & ESA & _).
unfold ev_wr. intros [Hw|[Hw|Hw]];  zl.
Qed.

(* ---- bytes ---- *)
Lemma ev_mb_kept : forall (W : world SEGS) mem mem' (P : Z -> Prop),
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  forall z, 0 <= z < 2 ^ 64 -> ~ P z -> mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z.
Proof. intros W mem mem' P H z Hz Hn. unfold mbyte. rewrite H; [reflexivity|]. rewrite unsigned_lit_small by zl. exact Hn. Qed.
Lemma ev_av_of_mb : forall (H H' : word -> bool) (m m' : word -> option byte) z,
  mbyte SEGS (mrestrict H' m') z = mbyte SEGS (mrestrict H m) z -> aview SEGS H' m' z = aview SEGS H m z.
Proof. intros H H' m m' z E. unfold aview. rewrite E. reflexivity. Qed.
Lemma ev_vm_kept : forall (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> mbyte SEGS m' (a + Z.of_nat k) = mbyte SEGS m (a + Z.of_nat k)) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v He Hv k Hk. rewrite (He k Hk). exact (Hv k Hk). Qed.
Lemma ev_garr8_kept : forall (m m' : word -> option byte) a l,
  (forall j, (j < length l)%nat -> mbyte SEGS m' (a + Z.of_nat j) = mbyte SEGS m (a + Z.of_nat j)) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof.
intros m m' a l He Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. assert (kk = 0%nat) by zl. subst kk. specialize (Hv 0%nat Hk). cbn [Z.of_nat] in *.
rewrite Z.add_0_r in *. rewrite (He j Hj). exact Hv.
Qed.
Lemma ev_sh_lt : forall x, 0 <= x < 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 < YM05.alloc_ceiling.
Proof.
intros x Hx. pose proof (asan_consts (rc := rc)) as (C1 & _). unfold SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(zl) ltac:(zl)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; zl). zl.
Qed.
Lemma ev_ra_kept : forall (rd rd' : reader) a len,
  (forall z, 0 <= z < YM05.alloc_ceiling -> rd' z = rd z) -> 0 <= a -> a + len <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a len -> range_addressable rd' SHADOW_OFF a len.
Proof.
intros rd rd' a len HK H0 H1 H. eapply range_addressable_agree; [|exact H].
intros x Hx. unfold shadow_of_addr. apply HK. apply ev_sh_lt. zl.
Qed.
Lemma ev_hull_kept : forall (rd rd' : reader) a len,
  (forall z, 0 <= z < YM05.alloc_ceiling -> rd' z = rd z) -> 0 <= a -> 0 < len -> a + len <= 2 ^ 47 ->
  shadow_hull_vis rd a len -> shadow_hull_vis rd' a len.
Proof.
intros rd rd' a len HK H0 Hl H1 H s Hs. rewrite HK; [exact (H s Hs)|].
pose proof (asan_consts (rc := rc)) as (C1 & _). unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos a 8 ltac:(zl) ltac:(zl)).
assert ((a + len - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; zl).
pose proof (Z.div_pos (2147450880 + a / 8) 8 ltac:(zl) ltac:(zl)).
assert ((2147450880 + (a + len - 1) / 8) / 8 < 2 ^ 42) by (apply Z.div_lt_upper_bound; zl). zl.
Qed.

(* the ledger survives a change above alloc_ceiling *)
Lemma ev_ledger_kept : forall ly S Hp W mem mem' memX md Lam peak cnt fail ran most own,
  ARx ly S Hp W memX md ->
  (forall z, 0 <= z < YM05.alloc_ceiling -> mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z) ->
  prh_ledger (PI := PIA) B ly S Hp W mem Lam peak cnt fail ran most own -> prh_ledger (PI := PIA) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' memX md Lam peak cnt fail ran most own HAR HK (HG & HND & HF & HPm).
pose proof (asan_consts (rc := rc)) as (C1 & _). pose proof (proj2 (@ASAN_CEIL_range rc)) as Cm. unfold ASAN_CEIL in Cm.
split; [|split; [exact HND|split; [|exact HPm]]].
- unfold prh_glob, prh_most, prh_own in *. cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most
    pi_g_own_ran_out pi_gz_live pi_gz_peak pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out
    prh_img_A] in *.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Gr).
  split; [eapply ev_vm_kept; [intros kk Hk; apply HK; zl | exact G1]|].
  split; [eapply ev_vm_kept; [intros kk Hk; apply HK; zl | exact G2]|].
  split; [eapply ev_vm_kept; [intros kk Hk; apply HK; zl | exact G3]|].
  split; [eapply ev_vm_kept; [intros kk Hk; apply HK; zl | exact G4]|].
  split; [eapply ev_vm_kept; [intros kk Hk; apply HK; zl | exact G5]|].
  (* #102: g_most / g_own_ran_out, the kit's two new ledger cells (PRH_Base.v 3004a98fe2d9 prh_most / prh_own) *)
  split; [split; [eapply ev_vm_kept; [intros kk Hk; apply HK; zl | exact G6] | exact G6r]|].
  split; [split; [eapply ev_vm_kept; [intros kk Hk; apply HK; zl | exact G7] | exact G7r]|]. exact Gr.
- rewrite Forall_forall in *. intros [a0 k0] Hin. destruct (HF _ Hin) as (Hk0 & Hab & Hhp & Ha16 & Hv). cbn [fst snd] in *.
  pose proof (@cf_head_nonneg cp) as Hh0.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W memX md _ _ HAR Hab) as (Hb16 & Hb4096 & Hbc & _).
  pose proof (req_size_pos (k0 + @cf_head cp) ltac:(zl)) as [R1 _].
  split; [exact Hk0|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
  eapply ev_vm_kept; [|exact Hv]. intros kk Hk. apply HK.
  pose proof (Z.div_mod (a0 - @cf_head cp) 16 ltac:(zl)). pose proof (Z.div_mod YM05.alloc_ceiling 16 ltac:(zl)).
  assert (YM05.alloc_ceiling mod 16 = 0) by (pose proof (Z.div_mod YM05.alloc_ceiling 4096 ltac:(zl)); pose proof (Z.mod_pos_bound YM05.alloc_ceiling 16 ltac:(zl)); zl).
  zl.
Qed.

(* a byte home of the tree (prhex_home) lies below 2 ^ 47 *)
Lemma ev_home_bound : forall ly S Hp W mem md memX Lam regs p n peak cnt fail ran most own,
  ARx ly S Hp W memX md -> prh_ledger (PI := PIA) B ly S Hp W mem Lam peak cnt fail ran most own -> ly_stk_hi ly <= 2 ^ 47 ->
  0 <= n -> prhex_home ly S Lam regs p n -> 0 <= p /\ p + n <= 2 ^ 47.
Proof.
intros ly S Hp W mem md memX Lam regs p n peak cnt fail ran most own HAR HL Hhi Hn H.
pose proof (asan_consts (rc := rc)) as (C1 & _). pose proof (@cf_head_nonneg cp) as Hh0.
destruct H as [(b & m & Hin & Hb & Hm) | [(cid & pos & Hin & Hf & Hfe) | (Hs & He)]].
- destruct HL as (_ & _ & HF & _). rewrite Forall_forall in HF. destruct (HF _ Hin) as (Hm0 & Hab & _). cbn [fst snd] in *.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W memX md _ _ HAR Hab) as (_ & Hb4096 & Hbc & _).
  pose proof (req_size_pos (m + @cf_head cp) ltac:(zl)) as [_ R2]. zl.
- destruct (alx_sep SEGS B ARx LAWS ly S Hp W memX md HAR) as (_ & HFs). rewrite Forall_forall in HFs.
  destruct (HFs _ Hin) as (F1 & F2). cbn [fst snd] in *. zl.
- unfold spZ in Hs. pose proof (bv_unsigned_in_range _ (getr regs 2)). zl.
Qed.

Lemma ev_saved_offs : forall orr, In orr EV_SAVED -> 152 <= fst orr <= 248.
Proof. intros orr H. cbv [EV_SAVED In] in H. repeat (destruct H as [<- | H]; [cbn; zl |]). destruct H. Qed.

(* ---- EV_MID across a straight-line stretch of ex_value's own code (only ev_wr bytes written) ---- *)
Lemma ev_mid_frame : forall a ly S Hp W mem md k p dep dl mem' md' k' p' dl',
  PRE a -> MID a ly S Hp W mem md k p dep dl ->
  AJ (STKa a + ea_d a) (sp0a a + ea_d a) (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly S Hp W mem' md' k' ->
  (forall x : word, ~ ev_wr a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 p' ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 32) 4 dl' ->
  YAkMemnorm.memnorm SEGS mem' ->
  MID a ly S Hp W mem' md' k' p' dep dl'.
Proof.
intros a ly S Hp W mem md k p dep dl mem' md' k' p' dl' HP HM HJ' HFr Hp' Hdl' HMN'.
pose proof (ev_arith a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinbs0 & _ & _ & Htree0 & _).
destruct HM as (HJ & Hwin & EHp & Eab & Hled & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & HRL & HRP & _).
pose proof HJ' as (HAR' & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof (ev_mb_kept W mem mem' (ev_wr a) HFr) as HK.
assert (HKc : forall z, 0 <= z < YM05.alloc_ceiling ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz. apply HK; [zl|]. apply ev_wr_ceil; [exact HP | zl]. }
assert (HKa : forall z, 0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z).
{ intros z Hz. apply ev_av_of_mb. apply HKc. exact Hz. }
split; [exact HJ'|].
split.
{ intros z Hz Hn. rewrite <- (Hwin z Hz Hn). apply ev_av_of_mb. apply HK; [zl|]. exact (ev_wr_win a z HP Hz Hn). }
split; [exact EHp|]. split; [exact Eab|].
split; [exact (ev_ledger_kept ly S Hp W mem mem' mem' md' _ _ _ _ _ _ _ HAR' HKc Hled)|].
split.
{ destruct Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
  split; [exact Hp'|].
  split; [eapply ev_vm_kept; [|exact Q2]; intros kk Hk; apply HK; [zl|]; apply (ev_wr_cur a _ HP); zl|].
  split; [eapply ev_vm_kept; [|exact Q3]; intros kk Hk; apply HK; [zl|]; apply (ev_wr_cur a _ HP); zl|].
  split; [eapply ev_vm_kept; [|exact Q4]; intros kk Hk; apply HK; [zl|]; apply (ev_wr_cur a _ HP); zl|].
  exact Hdl'. }
split.
{ destruct Hsrc as (Hg & H4 & Hc & Ham & Hra & Hhv). unfold ea_len in *.
  split; [|split; [exact H4|split; [exact Hc|split; [exact Ham|split]]]].
  - eapply ev_garr8_kept; [|exact Hg]. intros j Hj. apply HKc. zl.
  - eapply ev_ra_kept; [exact HKa | zl | zl | exact Hra].
  - intros Hl. eapply ev_hull_kept; [exact HKa | zl | exact Hl | zl | exact (Hhv Hl)]. }
split.
{ destruct Hwd as (W0' & W1 & W2 & W3 & W4 & W5). unfold ea_len in *.
  split; [exact W0'|]. split; [exact W1|]. split; [exact W2|]. split.
  - intros z Hz. destruct (W3 z Hz) as (Hwa & Hno & Hns). split; [|split; [exact Hno | exact Hns]].
    destruct Hinbs0 as (b & m & Hbm & Hb & Hbe & _). rewrite <- EHp in *. rewrite <- Eab in Hbm.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem' md' _ _ HAR' Hbm) as (_ & _ & _ & _ & Hpr & _).
    assert (Rm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); zl).
    apply (apresent_writable SEGS). apply (proj1 (Hpr z ltac:(zl))).
  - split.
    + eapply ev_ra_kept; [exact HKa | zl | zl | exact W4].
    + intros Hl. eapply ev_hull_kept; [exact HKa | zl | exact Hl | zl | exact (W5 Hl)]. }
split.
{ destruct Htree0 as [Hv0 | (Ht0 & HDpos & Hfoot)]; [left; exact Hv0|].
  destruct Htree as [Hv0 | (Hpj & Hhome & Hra & Hhv)]; [left; exact Hv0|]. right.
  pose proof (ev_home_bound ly S Hp W mem' md' mem' (ea_Lam a) (ea_regs a) (ea_v a) 56 _ _ _ _ _ _ HAR'
    (ev_ledger_kept ly S Hp W mem mem' mem' md' _ _ _ _ _ _ _ HAR' HKc Hled) ltac:(rewrite Eshi; zl) ltac:(zl) Hhome) as Hhb.
  (* a footprint byte is a machine address outside the bytes the stretch writes *)
  assert (Hfp : forall x, PRH_Reader.pj_footR (ea_v a) (ea_D a) x -> 0 <= x < 2 ^ 64 /\ ~ ev_wr a x).
  { intros x Hx. split.
    - destruct Hx as [Hn | ((xb, kb) & HinD & Hh)]; [zl|].
      pose proof (ev_node_blocks SEGS _ _ _ _ _ Hpj xb kb HinD) as HL. unfold prh_lin in HL.
      destruct Hled as (_ & _ & HF & _). rewrite Forall_forall in HF.
      destruct (HF _ HL) as (Hk0 & Hab & _). cbn [fst snd] in *.
      pose proof (@cf_head_nonneg cp) as Hh0.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem' md' _ _ HAR' Hab) as (_ & Hb4096 & Hbc & _).
      pose proof (req_size_pos (kb + @cf_head cp) ltac:(zl)) as [R1 R2].
      unfold PRH_Reader.pj_holdsR in Hh. cbn [fst snd] in Hh. zl.
    - intros Hw. destruct (Hfoot _ Hx) as (_ & Hnq & Hns & _). unfold ev_wr in Hw. unfold ea_sp0, ea_SA in *. zl. }
  split; [|split; [exact Hhome|split]].
  - apply (PRH_Reader.pj_nodeR_frame SEGS (ea_t a) _ _ _ _ _ Hpj).
    intros x Hx. destruct (Hfp x Hx) as (Hr & Hw).
    split; [exact (HK x Hr Hw)|].
    assert (E : mrestrict (w_H W) mem' (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
    { apply HFr. rewrite unsigned_lit_small by zl. exact Hw. }
    intros Hwa. unfold writable_at, LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview in *. rewrite E. exact Hwa.
  - eapply ev_ra_kept; [exact HKa | zl | zl | exact Hra].
  - eapply ev_hull_kept; [exact HKa | zl | zl | zl | exact Hhv]. }
split.
{ unfold ev_saved in *. rewrite Forall_forall in *. intros orr Hin. pose proof (ev_saved_offs orr Hin) as Ho.
  eapply ev_vm_kept; [|exact (Hsav orr Hin)]. intros kk Hk. apply HK; [zl|]. apply (ev_wr_saved a _ HP). zl. }
split.
{ rewrite <- Hflag. apply rdword_ext. intros kk Hk. apply HKa.
  assert (Hin : In (1, ea_pos a) (frames S)) by (rewrite Hfrs; left; reflexivity).
  destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem' md' HAR') as (_ & HFs). rewrite Forall_forall in HFs.
  destruct (HFs _ Hin) as (F1 & F2). cbn [fst snd] in *.
  assert (Efr : frame_addr ly 1 (ea_pos a) = fra a) by (unfold ea_fr, frame_addr; rewrite EF; reflexivity).
  rewrite Efr in F1, F2. change (fs_frame_bytes 1) with 128 in *. zl. }
split; [exact HRL|]. split; [exact HRP | exact HMN'].
Qed.

(* ---- piece 2's post, its internal cut, the engine at the activation's float state ---- *)
Definition ev_kind_pc (c off : Z) : Prop :=
  (c = 34 /\ off = EV_STR) \/ (c = 102 /\ off = EV_WORD_F) \/ (c = 110 /\ off = EV_WORD_N) \/ (c = 116 /\ off = EV_WORD_T) \/
  ((c = 123 \/ c = 91) /\ off = EV_ITEMS) \/
  (c <> 34 /\ c <> 91 /\ c <> 123 /\ c <> 102 /\ c <> 110 /\ c <> 116 /\ off = EV_NUM).
Definition ev_q2 (a : ev_act) : world SEGS -> config -> Prop :=
  fun W' c' => TO_EXIT a W' c' \/
    exists fx' regs' mem' md' ly' S' Hp' k' i1 c off,
      FXOK fx' /\ c' = CFG fx' regs' off mem' md' /\ AT_KIND a W' regs' mem' md' ly' S' Hp' k' i1 c /\ ev_kind_pc c off.
(* after the inlined ex_ws: in->p = x0 + i, the skip so far, a2 = in->end, the carriers of P_WS *)
Definition ev_c2 (a : ev_act) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (i : nat) : Prop :=
  MID a ly S Hp W mem md k (ea_x0 a + Z.of_nat i) (ea_dep a) (ea_dl a) /\ REGS a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 22 = w64 (fra a) /\ getr regs 23 = w64 (ea_v a) /\
  getr regs 12 = w64 (ea_x0 a + lena a) /\ (i <= length (ea_x a))%nat /\
  PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = PjGrammar.skip (skipn i (ea_x a)).
(* the loop head 0x833fc: a0 = a1 = in->p, a3 = 32, a4 = the blank mask, one more byte left *)
Definition ev_lp (a : ev_act) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (i : nat) : Prop :=
  ev_c2 a W regs mem md ly S Hp k i /\ (i < length (ea_x a))%nat /\
  getr regs 10 = w64 (ea_x0 a + Z.of_nat i) /\ getr regs 11 = w64 (ea_x0 a + Z.of_nat i) /\
  getr regs 13 = w64 32 /\ getr regs 14 = w64 EV_WSMASK.

Lemma ev_pc_eq : forall off, SIGMA AS_ex_value + off = BASE + (EV0 + off).
Proof.
intros off. assert (H1 : SIGMA AS_ex_value = A_prog_sigma AS_ex_value) by reflexivity.
assert (H2 : BASE = A_prog_base) by (vm_compute; reflexivity). rewrite H1, H2. unfold EV0. zl.
Qed.

Lemma ev_cfg_eq : forall fxc regs off mem md n, BASE + n = SIGMA AS_ex_value + off ->
  mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + n)) mem (YK11.seg_rom SEGS)) md = CFG fxc regs off mem md.
Proof. intros fxc regs off mem md n H. unfold ev_cfg, ev_pc. rewrite H. reflexivity. Qed.
Ltac ev_cfg_to off :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 (pa_val A_TEXT + ?n)) ?m _; cfg_model := ?d |} _ =>
    rewrite (ev_cfg_eq _ r off m d n ltac:(rewrite ev_pc_eq; vm_compute; reflexivity)) end.

Lemma ev_regs_kept : forall a regs regs', REGS a regs ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs' r = getr regs r) -> REGS a regs'.
Proof.
intros a regs regs' (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26) HK.
unfold ev_regs. rewrite !HK by (cbv; tauto). repeat split; assumption.
Qed.

(* the end of piece 2's first segment: in->p unchanged, registers kept, a2 = in->end *)
Lemma ev_c2_of_ws : forall a W regs mem md ly S Hp k regs' mem' md' k' (i : nat),
  PRE a -> MID a ly S Hp W mem md k (ea_x0 a + ea_i0 a) (ea_dep a) (ea_dl a) -> REGS a regs ->
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) -> getr regs 22 = w64 (fra a) -> getr regs 23 = w64 (ea_v a) ->
  AJ (STKa a + ea_d a) (sp0a a + ea_d a) (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly S Hp W mem' md' k' ->
  (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv -> getr regs' r = getr regs r) ->
  getr regs' 12 = w64 (ea_x0 a + lena a) -> Z.of_nat i = ea_i0 a ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_c2 a W regs' mem' md' ly S Hp k' i.
Proof.
intros a W regs mem md ly S Hp k regs' mem' md' k' i HP HM HR H20 H22 H23 HJ' Heq HK H12 Hi HMN'.
pose proof (ev_arith a HP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi0 & _).
pose proof HM as (_ & _ & _ & _ & _ & (Q1 & _ & _ & _ & Q5) & _).
split.
{ rewrite Hi. apply (ev_mid_frame a ly S Hp W mem md k _ _ _ mem' md' k' _ _ HP HM HJ').
  - intros x _. exact (Heq x).
  - exact (ev_vm_eq SEGS _ _ _ _ _ Heq Q1).
  - exact (ev_vm_eq SEGS _ _ _ _ _ Heq Q5).
  - exact HMN'. }
split; [apply (ev_regs_kept a regs regs' HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
split; [rewrite (HK 20%bv) by (cbv; tauto); exact H20|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact H22|].
split; [rewrite (HK 23%bv) by (cbv; tauto); exact H23|].
split; [exact H12|].
split; [unfold ea_len in Hi0; zl|].
f_equal. f_equal. rewrite <- Hi. apply Nat2Z.id.
Qed.


Lemma d_tail_end : forall a fxc W regs mem md ly S Hp k,
  PRE a -> FXOK fxc -> ev_c2 a W regs mem md ly S Hp k (length (ea_x a)) ->
  SRr SEGS W (CFG fxc regs EV_TL mem md) (ev_q2 a).
Proof.
intros a fxc W regs mem md ly S Hp k HP HFX (HM & HR & H20 & H22 & H23 & H12 & Hle & Hsk).
pose proof (ev_arith a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HM as (HJ & _ & _ & _ & _ & Hcur & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & _ & _ & _ & Q5).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
set (q := ea_q a) in *. set (x0 := ea_x0 a) in *. unfold ea_len in *.
set (len := Z.of_nat (length (ea_x a))) in *.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E19 : ew E 19 = w64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E26 : ew E 26 = w64 (shadow_addr q)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E12 : ew E 12 = w64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear EL.
assert (Hshq : 0 <= shadow_addr q < 2 ^ 46).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos q 8 ltac:(zl) ltac:(zl)). assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; zl). zl. }
assert (HS : st_ok_pi SEGS VAL E ss_te (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (EV0 + EV_TL))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_te. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E19. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 12 0) (x0 + len)); [exact (ev_denot_atom E 12 _ E12 ltac:(zl)) | zl | zl |].
      rewrite Z.add_0_r. exact Q1.
    + rewrite E26. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr q) 0 1 (SLit 0) 0); [reflexivity | zl | zl |].
      rewrite Z.add_0_r. apply ev_vm1_of_aview. unfold shadow_addr.
      apply (ZSB_x ly S Hp W mem md q HAR). rewrite Eslo, Eshi. zl.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19, E26. unfold w64. rewrite !unsigned_lit_small by zl.
    split; [split; [zl | exact I] | split; [exact I | exact I]].
  - split; [exact I | split; exact I]. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_EXIT).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  repeat (apply awr_ok_cons_ro; [cbn; zl|]). apply awr_ok_nil. }
pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi E _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27.
pmkst HS. ev_cfg_to EV_EXIT.
apply SRr_ret. left.
lazymatch goal with |- TO_EXIT a W (CFG fxc ?r EV_EXIT ?m ?d) => exists fxc, r, m, d, ly, S, Hp end.
eexists. exists (-1), len, (ea_dep a), (ea_dl a). split; [reflexivity|]. split; [exact HFX|].
split.
{ apply (ev_mid_frame a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ).
  - intros x _. exact (HM1 x).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q1).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q5).
  - exact HMN. }
split; [apply (ev_regs_kept a regs _ HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact H22|].
split; [rewrite N27; apply bv_eq; reflexivity|].
split; [exact Hdl|].
rewrite ev_V_blank; [split; [reflexivity | unfold ea_len; subst len; split; zl]|].
rewrite Hsk. rewrite skipn_all. reflexivity.
Qed.
(* ---- the tail-byte segment's run steps (state: q ro, s10 ro, the spill slot s1 + 112 writable, the byte ro) ---- *)
Ltac tb_awr E9 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end;
  apply awr_ok_cons_ro; [cbn; zl|]; apply awr_ok_cons_ro; [cbn; zl|];
  (eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat);
    [ reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite E9; unfold w64; rewrite unsigned_lit_small by zl; reflexivity
    | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; zl
    | apply awr_ok_cons_ro; [cbn; zl|]; apply awr_ok_nil ]).
Ltac tb_slot E9 :=
  let z := fresh "z" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros z (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try (cbn [ew ewset Nat.eqb] in Hr; rewrite E9 in Hr; unfold w64 in Hr; rewrite unsigned_lit_small in Hr by zl); zl|]);
  destruct Hin.
Ltac tb_step lo hi HMacc E9 :=
  let H := fresh "Hst" in
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (ev_frame_slot _ _ _ _ lo hi HFr ltac:(tb_slot E9)) as H end;
  let H2 := fresh "Hacc" in
  pose proof (fun x Hx => eq_trans (H x Hx) (HMacc x Hx)) as H2; clear H HMacc; rename H2 into HMacc;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.
Ltac brl c E33 H :=
  first [ rewrite (ev_blt_lit _ 33%nat c) in H; [ | cbn [ew ewset Nat.eqb]; exact E33 | zl | zl ]
        | rewrite (ev_beq_lit _ 33%nat c) in H; [ | cbn [ew ewset Nat.eqb]; exact E33 | zl | zl ]
        | rewrite (ev_bne_lit _ 33%nat c) in H; [ | cbn [ew ewset Nat.eqb]; exact E33 | zl | zl ] ].

Ltac lp_awr E19 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end;
  (eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat);
    [ reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite E19; unfold w64; rewrite unsigned_lit_small by zl; reflexivity
    | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; zl
    | apply awr_ok_cons_ro; [cbn; zl|]; apply awr_ok_cons_ro; [cbn; zl|]; apply awr_ok_nil ]).

(* the switch's leaves: P_KIND with the byte c in s5, in->p in a1, in->end in a2, s11 = -1; only s1 + 112 written *)
Lemma ev_kind_of_tb : forall a W regs mem md ly S Hp k i regs' mem' md' k',
  PRE a -> ev_c2 a W regs mem md ly S Hp k i -> (i < length (ea_x a))%nat -> PjGrammar.ws (nth i (ea_x a) 0) = false ->
  AJ (STKa a + ea_d a) (sp0a a + ea_d a) (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly S Hp W mem' md' k' ->
  (forall x : word, ~ (S1a a + 112 <= bv_unsigned x < S1a a + 120) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv -> getr regs' r = getr regs r) ->
  getr regs' 11 = w64 (ea_x0 a + Z.of_nat i) -> getr regs' 12 = w64 (ea_x0 a + lena a) ->
  getr regs' 21 = w64 (nth i (ea_x a) 0) -> getr regs' 27 = w64 (-1) ->
  YAkMemnorm.memnorm SEGS mem' ->
  AT_KIND a W regs' mem' md' ly S Hp k' i (nth i (ea_x a) 0).
Proof.
intros a W regs mem md ly S Hp k i regs' mem' md' k' HP (HM & HR & H20 & H22 & H23 & H12 & Hle & Hsk) Hi Hws HJ' Hfr HK
  N11 N12 N21 N27 HMN'.
pose proof (ev_arith a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & _).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HM as (_ & _ & _ & _ & _ & (Q1 & _ & _ & _ & Q5) & _).
assert (HK2 : forall z, 0 <= z < 2 ^ 64 -> ~ (S1a a + 112 <= z < S1a a + 120) ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z) by exact (ev_mb_kept W mem mem' _ Hfr).
split.
{ apply (ev_mid_frame a ly S Hp W mem md k _ _ _ mem' md' k' _ _ HP HM HJ').
  - intros x Hx. apply Hfr. intros Hs. apply Hx. unfold ev_wr. left. zl.
  - eapply ev_vm_kept; [|exact Q1]. intros kk Hk. apply HK2; zl.
  - eapply ev_vm_kept; [|exact Q5]. intros kk Hk. apply HK2; zl.
  - exact HMN'. }
split; [apply (ev_regs_kept a regs regs' HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
split; [rewrite (HK 20%bv) by (cbv; tauto); exact H20|].
split; [exact N21|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact H22|].
split; [rewrite (HK 23%bv) by (cbv; tauto); exact H23|].
split; [exact N27|]. split; [exact N11|]. split; [exact N12|].
split; [exact Hi|]. split; [reflexivity|]. split; [exact Hws|].
rewrite Hsk, (ev_skipn_cons _ i Hi). cbn [PjGrammar.skip]. rewrite Hws. reflexivity.
Qed.

Lemma d_tail_byte : forall a fxc W regs mem md ly S Hp k i,
  PRE a -> FXOK fxc -> ev_c2 a W regs mem md ly S Hp k i -> (i < length (ea_x a))%nat ->
  PjGrammar.ws (nth i (ea_x a) 0) = false ->
  SRr SEGS W (CFG fxc regs EV_TL mem md) (ev_q2 a).
Proof.
intros a fxc W regs mem md ly S Hp k i HP HFX HC2 Hi Hws.
pose proof HC2 as (HM & HR & H20 & H22 & H23 & H12 & Hle & Hsk).
pose proof (ev_arith a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinb0 & _).
pose proof HM as (HJ & _ & EHp & Eab & _ & Hcur & Hsrc & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & _ & _ & _ & Q5).
pose proof Hsrc as (Hg & _ & _ & _ & Hra & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
set (c := nth i (ea_x a) 0) in *.
assert (Hc8 : 0 <= c < 256) by (exact (proj2 (Hg i Hi))).
assert (Hcv : val_mem SEGS (mrestrict (w_H W) mem) (ea_x0 a + Z.of_nat i) 1 c) by (exact (proj1 (Hg i Hi))).
(* the text lies in an allocator block: an application address apart from the shadow *)
assert (Happ : in_app (ea_x0 a + Z.of_nat i) 1).
{ destruct (Hinb0 ltac:(unfold ea_len; zl)) as (b & m & Hbm & Hb & Hbe & _). rewrite <- Eab in Hbm.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbm) as (_ & _ & _ & Happ & _).
  assert (Rm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); zl).
  apply (in_app_sub b (req_size m)); [exact Happ | zl | zl | unfold ea_len in Hbe; zl]. }
set (q := ea_q a) in *. set (x0 := ea_x0 a) in *. unfold ea_len in *.
set (len := Z.of_nat (length (ea_x a))) in *.
remember (Eimg (Ereg regs [w64 (x0 + Z.of_nat i); w64 c])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 (x0 + Z.of_nat i); w64 c]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = w64 (S1a a)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = w64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = w64 (shadow_addr q)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E12 : ew E 12 = w64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = w64 (x0 + Z.of_nat i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs [w64 (x0 + Z.of_nat i); w64 c]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear EL.
assert (Hshq : SHADOW_OFF + 2 ^ 44 - 2 ^ 41 <= shadow_addr q < SHADOW_OFF + 2 ^ 44).
{ unfold shadow_addr. assert (2 ^ 44 - 2 ^ 41 <= q / 8) by (apply Z.div_le_lower_bound; zl).
  assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; zl). zl. }
unfold SHADOW_OFF in Hshq.
assert (HS : st_ok_pi SEGS VAL E ss_tb (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (EV0 + EV_TL))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tb. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E19. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) (x0 + Z.of_nat i)); [exact (ev_denot_atom E 32 _ E32 ltac:(zl)) | zl | zl |].
      rewrite Z.add_0_r. exact Q1.
    + rewrite E26. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr q) 0 1 (SLit 0) 0); [reflexivity | zl | zl |].
      rewrite Z.add_0_r. apply ev_vm1_of_aview. unfold shadow_addr.
      apply (ZSB_x ly S Hp W mem md q HAR). rewrite Eslo, Eshi. zl.
    + rewrite E9. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. zl.
    + rewrite E32. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x0 + Z.of_nat i) 0 1 (SOff 33 0) c); [exact (ev_denot_atom E 33 _ E33 ltac:(zl)) | zl | zl |].
      rewrite Z.add_0_r. exact Hcv.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19, E26, E9, E32. unfold w64. rewrite !unsigned_lit_small by zl.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Happ, Hshq.
    repeat split; zl.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E24, E9, E32, E33, E12. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; zl).
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r. unfold D_QLO.
    repeat split; zl. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx SH_tb E (mrestrict (w_H W) mem)).
{ constructor; [|constructor]. split.
  - unfold D_Bx. cbn [she_m she_lo she_hi]. rewrite (U_atom E 24 _ E24) by (unfold SHADOW_OFF; zl). rewrite (U_atom E 32 _ E32) by zl.
    apply (range_addressable_sub _ _ x0 len); [exact Hra | zl | zl].
  - intros z Hz. unfold D_Bx in *. cbn [she_m she_lo she_hi] in Hz.
    rewrite (U_atom E 24 _ E24) by (unfold SHADOW_OFF; zl). rewrite (U_atom E 32 _ E32) in Hz by zl.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Happ |- *. zl. }
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUN := @paj_run_x fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNTO := @paj_run_to_x fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  apply awr_ok_cons_ro; [cbn; zl|]. apply awr_ok_cons_ro; [cbn; zl|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat (S1a a)); [reflexivity | rewrite E9; unfold w64; rewrite unsigned_lit_small by zl; reflexivity | |].
  - intros z Hz. cbn [YP09.r_wlo YP09.r_whi] in Hz. left. zl.
  - apply awr_ok_cons_ro; [cbn; zl|]. apply awr_ok_nil. }
pose proof (ev_frame_slot _ _ _ _ (S1a a + 112) (S1a a + 120) HFr ltac:(tb_slot E9)) as HMacc. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK D_Bspan.
{ (* in->p >= in->end: impossible before a byte *)
  exfalso. rewrite branch_geu_U in Hc. uat 32%nat (x0 + Z.of_nat i) E32 Hc. uat 12%nat (x0 + len) E12 Hc.
  apply negb_true_iff, Z.ltb_ge in Hc. subst len. zl. }
rewrite branch_geu_U in Hc. uat 32%nat (x0 + Z.of_nat i) E32 Hc. uat 12%nat (x0 + len) E12 Hc. clear Hc.
paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [tb_awr E9|]. tb_step (S1a a + 112) (S1a a + 120) HMacc E9.
psrr_branch_tok RUN BR HS SHOK D_Bspan; brl c E33 Hc.
- (* 109 < c *)
  apply Z.ltb_lt in Hc. rename Hc into Hg109.
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [tb_awr E9|]. tb_step (S1a a + 112) (S1a a + 120) HMacc E9.
  psrr_branch_tok RUN BR HS SHOK D_Bspan; brl c E33 Hc.
  + apply Z.eqb_eq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_WORD_N); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_WORD_N;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_WORD_N; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ]. right; right; left; split; [exact Hc | reflexivity].
  + apply Z.eqb_neq in Hc. rename Hc into Hn110.
    paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [tb_awr E9|]. tb_step (S1a a + 112) (S1a a + 120) HMacc E9.
    psrr_branch_tok RUN BR HS SHOK D_Bspan; brl c E33 Hc.
    * apply Z.eqb_eq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_WORD_T); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_WORD_T;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_WORD_T; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ]. right; right; right; left; split; [exact Hc | reflexivity].
    * apply Z.eqb_neq in Hc. rename Hc into Hn116.
      paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [tb_awr E9|]. tb_step (S1a a + 112) (S1a a + 120) HMacc E9.
      psrr_branch_tok RUN BR HS SHOK D_Bspan; brl c E33 Hc.
      -- apply negb_true_iff, Z.eqb_neq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_NUM); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_NUM;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_NUM; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ].
         right; right; right; right; right. repeat split; zl.
      -- apply negb_false_iff, Z.eqb_eq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_ITEMS); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_ITEMS;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_ITEMS; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ].
         right; right; right; right; left. split; [left; exact Hc | reflexivity].
- (* c <= 109 *)
  apply Z.ltb_ge in Hc. rename Hc into Hl109.
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [tb_awr E9|]. tb_step (S1a a + 112) (S1a a + 120) HMacc E9.
  psrr_branch_tok RUN BR HS SHOK D_Bspan; brl c E33 Hc.
  + apply Z.eqb_eq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_STR); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_STR;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_STR; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ]. left; split; [exact Hc | reflexivity].
  + apply Z.eqb_neq in Hc. rename Hc into Hn34.
    paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [tb_awr E9|]. tb_step (S1a a + 112) (S1a a + 120) HMacc E9.
    psrr_branch_tok RUN BR HS SHOK D_Bspan; brl c E33 Hc.
    * apply Z.eqb_eq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_ITEMS); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_ITEMS;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_ITEMS; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ]. right; right; right; right; left. split; [right; exact Hc | reflexivity].
    * apply Z.eqb_neq in Hc. rename Hc into Hn91.
      paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [tb_awr E9|]. tb_step (S1a a + 112) (S1a a + 120) HMacc E9.
      psrr_branch_tok RUN BR HS SHOK D_Bspan; brl c E33 Hc.
      -- apply negb_true_iff, Z.eqb_neq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_NUM); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_NUM;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_NUM; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ].
         right; right; right; right; right. repeat split; zl.
      -- apply negb_false_iff, Z.eqb_eq in Hc. paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_WORD_F); [tb_awr E9|]; tb_step (S1a a + 112) (S1a a + 120) HMacc E9;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
  prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (21%bv : bv 5) N21; prreg HS (27%bv : bv 5) N27;
  rewrite ?E32 in N11; rewrite ?E12 in N12; rewrite ?E33 in N21;
  pmkst HS; ev_cfg_to EV_WORD_F;
  apply SRr_ret; right;
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, _ /\ CFG _ ?r _ ?m ?d = _ /\ _ =>
    exists fxc, r, m, d, ly, S, Hp end;
  eexists; exists i, c, EV_WORD_F; split; [exact HFX|]; split; [reflexivity|]; split;
  [ apply (ev_kind_of_tb a W regs mem md ly S Hp k i _ _ _ _ HP HC2 Hi Hws HJ HMacc HK N11 ltac:(exact N12) N21
      ltac:(rewrite N27; apply bv_eq; reflexivity) HMN) | unfold ev_kind_pc ]. right; left; split; [exact Hc | reflexivity].
Qed.
(* a loop step's or exit's end: only in->p written, registers kept *)
Lemma ev_c2_of_lp : forall a W regs mem md ly S Hp k i j regs' mem' md' k',
  PRE a -> ev_c2 a W regs mem md ly S Hp k i ->
  AJ (STKa a + ea_d a) (sp0a a + ea_d a) (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly S Hp W mem' md' k' ->
  (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 (ea_x0 a + Z.of_nat j) ->
  (forall r, In r [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 23; 24; 25; 26]%bv -> getr regs' r = getr regs r) ->
  (j <= length (ea_x a))%nat -> PjGrammar.skip (skipn i (ea_x a)) = PjGrammar.skip (skipn j (ea_x a)) ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_c2 a W regs' mem' md' ly S Hp k' j.
Proof.
intros a W regs mem md ly S Hp k i j regs' mem' md' k' HP (HM & HR & H20 & H22 & H23 & H12 & Hle & Hsk) HJ' Hfr Hp' HK Hj Hsk' HMN'.
pose proof (ev_arith a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & _).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HM as (_ & _ & _ & _ & _ & (Q1 & _ & _ & _ & Q5) & _).
assert (HK2 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z) by exact (ev_mb_kept W mem mem' _ Hfr).
split.
{ apply (ev_mid_frame a ly S Hp W mem md k _ _ _ mem' md' k' _ _ HP HM HJ').
  - intros x Hx. apply Hfr. intros Hs. apply Hx. unfold ev_wr. right; left. zl.
  - exact Hp'.
  - eapply ev_vm_kept; [|exact Q5]. intros kk Hk. apply HK2; zl.
  - exact HMN'. }
split; [apply (ev_regs_kept a regs regs' HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
split; [rewrite (HK 20%bv) by (cbv; tauto); exact H20|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact H22|].
split; [rewrite (HK 23%bv) by (cbv; tauto); exact H23|].
split; [rewrite (HK 12%bv) by (cbv; tauto); exact H12|].
split; [exact Hj|]. rewrite Hsk. exact Hsk'.
Qed.

Lemma d_loop : forall m a fxc W regs mem md ly S Hp k i, (length (ea_x a) - i = m)%nat ->
  PRE a -> FXOK fxc -> ev_lp a W regs mem md ly S Hp k i ->
  SRr SEGS W (CFG fxc regs EV_LP mem md) (ev_q2 a).
Proof.
induction m as [|m IH]; intros a fxc W regs mem md ly S Hp k i Hm HP HFX (HC2 & Hi & N10 & N11 & N13 & N14); [zl|].
pose proof HC2 as (HM & HR & H20 & H22 & H23 & H12 & Hle & Hsk).
pose proof (ev_arith a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinb0 & _).
pose proof HM as (HJ & _ & EHp & Eab & _ & Hcur & Hsrc & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & _ & _ & _ & Q5).
pose proof Hsrc as (Hg & _ & _ & _ & Hra & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
set (c := nth i (ea_x a) 0) in *.
assert (Hc8 : 0 <= c < 256) by (exact (proj2 (Hg i Hi))).
assert (Hcv : val_mem SEGS (mrestrict (w_H W) mem) (ea_x0 a + Z.of_nat i) 1 c) by (exact (proj1 (Hg i Hi))).
assert (Happ : in_app (ea_x0 a + Z.of_nat i) 1).
{ destruct (Hinb0 ltac:(unfold ea_len; zl)) as (b & m0 & Hbm & Hb & Hbe & _). rewrite <- Eab in Hbm.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbm) as (_ & _ & _ & Happ & _).
  assert (Rm : m0 <= req_size m0) by (unfold req_size; destruct (Z.eqb_spec m0 0); zl).
  apply (in_app_sub b (req_size m0)); [exact Happ | zl | zl | unfold ea_len in Hbe; zl]. }
set (q := ea_q a) in *. set (x0 := ea_x0 a) in *. unfold ea_len in *.
set (len := Z.of_nat (length (ea_x a))) in *.
remember (Eimg (Ereg regs [w64 (x0 + Z.of_nat i); w64 c])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 (x0 + Z.of_nat i); w64 c]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E19 : ew E 19 = w64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = w64 (shadow_addr q)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E12 : ew E 12 = w64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = w64 (x0 + Z.of_nat i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs [w64 (x0 + Z.of_nat i); w64 c]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear EL.
assert (Hshq : SHADOW_OFF + 2 ^ 44 - 2 ^ 41 <= shadow_addr q < SHADOW_OFF + 2 ^ 44).
{ unfold shadow_addr. assert (2 ^ 44 - 2 ^ 41 <= q / 8) by (apply Z.div_le_lower_bound; zl).
  assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; zl). zl. }
unfold SHADOW_OFF in Hshq.
assert (HS : st_ok_pi SEGS VAL E ss_lp (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (EV0 + EV_LP))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lp. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [|discriminate|exact N14].
    apply regs_ok_pin; [|discriminate|exact N13].
    apply regs_ok_pin; [|discriminate|rewrite N11; symmetry; exact (ev_denot_atom E 32 _ E32 ltac:(zl))].
    apply regs_ok_pin; [|discriminate|rewrite N10; symmetry; exact (ev_denot_atom E 32 _ E32 ltac:(zl))].
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E19. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply Hpres. zl.
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) (x0 + Z.of_nat i)); [exact (ev_denot_atom E 32 _ E32 ltac:(zl)) | zl | zl |].
        rewrite Z.add_0_r. exact Q1.
    + rewrite E26. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr q) 0 1 (SLit 0) 0); [reflexivity | zl | zl |].
      rewrite Z.add_0_r. apply ev_vm1_of_aview. unfold shadow_addr.
      apply (ZSB_x ly S Hp W mem md q HAR). rewrite Eslo, Eshi. zl.
    + rewrite E32. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x0 + Z.of_nat i) 0 1 (SOff 33 0) c); [exact (ev_denot_atom E 33 _ E33 ltac:(zl)) | zl | zl |].
      rewrite Z.add_0_r. exact Hcv.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19, E26, E32. unfold w64. rewrite !unsigned_lit_small by zl.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    repeat split; zl.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E24, E19, E32, E33, E12. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; zl).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. unfold D_QLO.
    repeat split; zl. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx SH_tb E (mrestrict (w_H W) mem)).
{ constructor; [|constructor]. split.
  - unfold D_Bx. cbn [she_m she_lo she_hi]. rewrite (U_atom E 24 _ E24) by (unfold SHADOW_OFF; zl). rewrite (U_atom E 32 _ E32) by zl.
    apply (range_addressable_sub _ _ x0 len); [exact Hra | zl | zl].
  - intros z Hz. unfold D_Bx in *. cbn [she_m she_lo she_hi] in Hz.
    rewrite (U_atom E 24 _ E24) by (unfold SHADOW_OFF; zl). rewrite (U_atom E 32 _ E32) in Hz by zl.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Happ |- *. zl. }
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUN := @paj_run_x fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNTO := @paj_run_to_x fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [lp_awr E19|].
pose proof (ev_frame_slot _ _ _ _ q (q + 8) HFr ltac:(tb_slot E19)) as HMacc. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK D_Bspan; rewrite branch_ltu_U, U_SLit in Hc; uat 33%nat c E33 Hc; change (zcanon 32) with 32 in Hc.
- (* 32 < c: not a blank, the loop ends at i *)
  apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_TL); [lp_awr E19|]. tb_step q (q + 8) HMacc E19.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK.
  lp_inp HS E19 E32. rewrite Z.add_0_r in Hp'.
  pmkst HS. ev_cfg_to EV_TL.
  eapply (d_tail_byte a fxc W _ _ _ ly S Hp _ i HP HFX); [| exact Hi | apply ev_ws_big; exact Hc].
  apply (ev_c2_of_lp a W regs mem md ly S Hp k i i _ _ _ _ HP HC2 HJ HMacc Hp' HK); [zl | reflexivity | exact HMN].
- apply Z.ltb_ge in Hc. rename Hc into Hc32.
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [lp_awr E19|]. tb_step q (q + 8) HMacc E19.
  psrr_branch_tok RUN BR HS SHOK D_Bspan; rewrite (ev_mask_br _ 33%nat c) in Hc;
    [ | cbn [ew ewset Nat.eqb]; exact E33 | zl | | cbn [ew ewset Nat.eqb]; exact E33 | zl ].
  + (* the mask bit is 0: not a blank *)
    apply negb_true_iff in Hc.
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_TL); [lp_awr E19|]. tb_step q (q + 8) HMacc E19.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK.
    lp_inp HS E19 E32. rewrite Z.add_0_r in Hp'.
    pmkst HS. ev_cfg_to EV_TL.
    eapply (d_tail_byte a fxc W _ _ _ ly S Hp _ i HP HFX); [| exact Hi | exact Hc].
    apply (ev_c2_of_lp a W regs mem md ly S Hp k i i _ _ _ _ HP HC2 HJ HMacc Hp' HK); [zl | reflexivity | exact HMN].
  + (* a blank: in->p = x0 + i + 1 stored *)
    apply negb_false_iff in Hc. rename Hc into Hwsc.
    assert (Hsk1 : PjGrammar.skip (skipn i (ea_x a)) = PjGrammar.skip (skipn (Datatypes.S i) (ea_x a))).
    { rewrite (ev_skipn_cons _ i Hi). cbn [PjGrammar.skip]. fold c. rewrite Hwsc. reflexivity. }
    paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan; [lp_awr E19|]. tb_step q (q + 8) HMacc E19.
    psrr_branch_tok RUN BR HS SHOK D_Bspan; rewrite branch_ne_U in Hc;
      rewrite (U_atom_off _ 32%nat (x0 + Z.of_nat i) 1) in Hc by (try (cbn [ew ewset Nat.eqb]; exact E32); zl);
      uat 12%nat (x0 + len) E12 Hc.
    * (* not at the end: the next iteration *)
      apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_LP); [lp_awr E19|]. tb_step q (q + 8) HMacc E19.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK.
      prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11. prreg HS (13%bv : bv 5) M13. prreg HS (14%bv : bv 5) M14.
      lp_inp HS E19 E32.
      pmkst HS. ev_cfg_to EV_LP.
      assert (Hm' : (length (ea_x a) - Datatypes.S i = m)%nat).
      { clear - Hm Hi Hc. zl. }
      eapply (IH a fxc W _ _ _ ly S Hp _ (Datatypes.S i) Hm' HP HFX).
      split; [|split; [subst len; zl|]].
      -- apply (ev_c2_of_lp a W regs mem md ly S Hp k i (Datatypes.S i) _ _ _ _ HP HC2 HJ HMacc); [| exact HK | zl | exact Hsk1 | exact HMN].
         rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat i)) with (Z.of_nat i + 1) by zl. rewrite Z.add_assoc. exact Hp'.
      -- rewrite Nat2Z.inj_succ.
         rewrite E32 in M10, M11. unfold w64 in M10, M11. rewrite unsigned_lit_small in M10, M11 by zl.
         split; [rewrite M10; unfold w64; f_equal; zl|]. split; [rewrite M11; unfold w64; f_equal; zl|].
         split; [exact M13 | exact M14].
    * (* at the end: in->p = in->end *)
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_TL); [lp_awr E19|]. tb_step q (q + 8) HMacc E19.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK.
      lp_inp HS E19 E32.
      pmkst HS. ev_cfg_to EV_TL.
      assert (EL : Datatypes.S i = length (ea_x a)) by (subst len; zl).
      eapply (d_tail_end a fxc W _ _ _ ly S Hp _ HP HFX).
      rewrite <- EL.
      apply (ev_c2_of_lp a W regs mem md ly S Hp k i (Datatypes.S i) _ _ _ _ HP HC2 HJ HMacc); [| exact HK | zl | exact Hsk1 | exact HMN].
      rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat i)) with (Z.of_nat i + 1) by zl. rewrite Z.add_assoc. exact Hp'.
Qed.

(* piece 2's first segment: P_WS -> the loop head (in->p < in->end) or the end test (in->p = in->end) *)
Lemma d_ws : forall a fxc W regs mem md ly S Hp k,
  PRE a -> FXOK fxc -> AT_WS a W regs mem md ly S Hp k ->
  SRr SEGS W (CFG fxc regs EV_WS mem md) (ev_q2 a).
Proof.
intros a fxc W regs mem md ly S Hp k HP HFX (HM & HR & H20 & H22 & H23).
pose proof (ev_arith a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HM as (HJ & _ & _ & _ & _ & Hcur & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & Q2 & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
set (q := ea_q a) in *. set (x0 := ea_x0 a) in *. unfold ea_len in *.
set (len := Z.of_nat (length (ea_x a))) in *.
remember (Eimg (Ereg regs [w64 (x0 + ea_i0 a); w64 (x0 + len)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 (x0 + ea_i0 a); w64 (x0 + len)]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E19 : ew E 19 = w64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E26 : ew E 26 = w64 (shadow_addr q)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = w64 (x0 + ea_i0 a)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs [w64 (x0 + ea_i0 a); w64 (x0 + len)]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear EL.
assert (Hshq : 0 <= shadow_addr q < 2 ^ 46).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos q 8 ltac:(zl) ltac:(zl)). assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; zl). zl. }
assert (HS : st_ok_pi SEGS VAL E ss_ws (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (EV0 + EV_WS))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ws. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E19. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) (x0 + ea_i0 a)); [exact (ev_denot_atom E 32 _ E32 ltac:(zl)) | zl | zl |].
        rewrite Z.add_0_r. exact Q1.
      * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) (x0 + len)); [exact (ev_denot_atom E 33 _ E33 ltac:(zl)) | zl | zl |].
        exact Q2.
    + rewrite E26. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr q) 0 1 (SLit 0) 0); [reflexivity | zl | zl |].
      rewrite Z.add_0_r. apply ev_vm1_of_aview. unfold shadow_addr.
      apply (ZSB_x ly S Hp W mem md q HAR). rewrite Eslo, Eshi. zl.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19, E26. unfold w64. rewrite !unsigned_lit_small by zl.
    split; [split; [zl | exact I] | split; [exact I | exact I]].
  - split; [exact I | split; exact I]. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUN := @paj_run_x fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNTO := @paj_run_to_x fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  repeat (apply awr_ok_cons_ro; [cbn; zl|]). apply awr_ok_nil. }
pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK D_Bspan.
- (* in->p >= in->end: the text is used up, i0 = len *)
  rewrite branch_geu_U, (U_atom E 32 _ E32 ltac:(zl)), (U_atom E 33 _ E33 ltac:(zl)) in Hc.
  assert (Hi0e : ea_i0 a = len) by (apply negb_true_iff in Hc; apply Z.ltb_ge in Hc; zl).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_TL).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
      change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
    repeat (apply awr_ok_cons_ro; [cbn; zl|]). apply awr_ok_nil. }
  pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM2. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (12%bv : bv 5) N12. rewrite E33 in N12.
  pmkst HS. ev_cfg_to EV_TL.
  eapply (d_tail_end a fxc W _ _ _ ly S Hp _ HP HFX).
  apply (ev_c2_of_ws a W regs mem md ly S Hp k _ _ _ _ _ HP HM HR H20 H22 H23 HJ).
  + intros x. rewrite HM2. exact (HM1 x).
  + exact HK.
  + unfold ea_len. exact N12.
  + subst len. zl.
  + exact HMN.
- (* in->p < in->end: into the loop *)
  rewrite branch_geu_U, (U_atom E 32 _ E32 ltac:(zl)), (U_atom E 33 _ E33 ltac:(zl)) in Hc.
  assert (Hi0l : ea_i0 a < len) by (apply negb_false_iff in Hc; apply Z.ltb_lt in Hc; zl).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_LP).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
      change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
    repeat (apply awr_ok_cons_ro; [cbn; zl|]). apply awr_ok_nil. }
  pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM2. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
  prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
  rewrite E32 in N10, N11. rewrite E33 in N12.
  pmkst HS. ev_cfg_to EV_LP.
  eapply (d_loop (length (ea_x a) - Z.to_nat (ea_i0 a)) a fxc W _ _ _ ly S Hp _ (Z.to_nat (ea_i0 a)) eq_refl HP HFX).
  split; [|split; [subst len; zl|]].
  + apply (ev_c2_of_ws a W regs mem md ly S Hp k _ _ _ _ _ HP HM HR H20 H22 H23 HJ).
    * intros x. rewrite HM2. exact (HM1 x).
    * exact HK.
    * unfold ea_len. exact N12.
    * zl.
    * exact HMN.
  + rewrite Z2Nat.id by zl. split; [exact N10|]. split; [exact N11|]. split; [exact N13|]. exact N14.
Qed.

End w.
