(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane: the asan-ubsan twin of libreac/fuzz_knock lib/A/AD3g.v
   at 48907dc7e8ca (by a Theorem Labs lane, the S7 prover, with amendment 11 to the statement's approval), the statement of
   __sanitizer::TwoLevelMap<StackDepotNode,32768,65536,LocalAddressSpaceView>::Create (0x71714-0x71814, 64 insns, YB1w.v
   tfib_A_TwoLevelMap_Create_71714, fuzz_knock.asan-ubsan sha256 f834165f5002...) on knock's first-use path, and its proof.
   rule 24: proves function TwoLevelMap<StackDepotNode,32768,65536,LocalAddressSpaceView>::Create (asan-ubsan); reuse
   search proof-index (tfib_tlm_create_nb_ok mod_contract mod_holds mnr_contract 0x71714 0x64278 0x647b0 0x64f54)
   and git grep over the knock working branches; second-agent check by a Theorem Labs lane CONFIRM 2026-10-29 (no lib/AU twin existed).
   The statement and the Section premises are AD3g's under the AU name map only: lib/A/AXyz -> lib/AU/YXyz (lib/AU keeps
   the name AWalkFw0, as derive_y.py makes it and lib/AU/YD3h.v requires it), AD3d -> YD3d, AD3h -> YD3h (lib/AU/YD3h.v,
   by a Theorem Labs lane); the Reusable Requires are unchanged. The proof is AD3g's with these numerals re-measured on the
   asan-ubsan pin (sha256 f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82) against the asan pin (sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118):
   - theDepot 0x180418 -> 0x180458 (nm; auipc/addi at 0x70d70/0x70d74 and 0x70ef4/0x70ef8; YF0m.v TFIB_DEPOT), so the
     mutex word MUv = TFIB_DEPOT + tlm_mu 0x580420 -> 0x580460, map1_[0] CXv = TFIB_DEPOT + d_map1 0x580428 -> 0x580468,
     and the bound below MUv that carries mod_cells over phase A 0x580420 -> 0x580460.
   - Create's 64 insns are byte-identical but 0x71774 (ld s2 of the page-size GOT slot: 0x965b0 -> 0x965f8, whose word is
     0x12dfe0 -> 0x12e020 = PageSizeCached), read here through YD3h's MOD_PSC_GOT / MOD_PSC.
   - Unchanged: the code addresses (0x71714, 0x717b8 = 464824, MmapOrDie 0x64278), the image end TFIB_IMG_END =
     YImgTop.IMG_TOP = 0x5f3000 (YF0x.v:27; Reusable/YImgTop.v:5) and the writable window's low end 0x96000 (rw7, from
     YB1h.v:87-88 tfib_rw_window: LOAD 0x96088 page-rounded, 8192 + 5615616 bytes to
     0x5f3000, YB1h.v:80-83).
   lib/AU/YF0m.v (TfibSyms, TFIB_DEPOT) was not on the base this file was written on: it built from
   YF0m.v (sha256 77ff7f6e6d76; internal record), a build-only input. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YK0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YF0m YF0x YB1w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0h YK14 YK1b YK1a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YB1h YB1q YFl0 YFl3 YFek YFel.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YD3d YD3h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* md_takes and md_room: lib/AU/YD3d.v. MOD_STK, mod_cells, mod_room, mod_contract and mod_holds: lib/AU/YD3h.v. *)

(* a Theorem Labs lane's helper, verbatim (internal path:21-23). Encoding of "nodes block not yet
   mapped": ly_NB ly = 0. *)
Definition set_ly_NB (ly : alayout) (nb : Z) : alayout :=
ALayout (ly_prim ly) (ly_space ly) (ly_Q ly) (ly_T ly) (ly_C ly) (ly_F ly) nb (ly_SB ly) (ly_top ly)
(ly_stk_lo ly) (ly_stk_hi ly) (ly_tsd ly) (ly_tr0 ly) (ly_extra ly) (ly_D ly) (ly_vis0 ly) (ly_img ly) (ly_sec ly).

(* static_extents ly (YG0f.v:388-389) without the nodes block's own entry (ly_NB ly, kNodesBlockSize), and with the
   store block's entry only once it is mapped: Put creates the nodes block (0x7118c) BEFORE StackStore creates the store
   block (Node::store 0x71114 -> Store -> Alloc -> BlockInfo::Create), so on knock's first Put ly_SB ly = 0 here too, and
   both unmapped entries are the empty extent (4096, 0) (YG0f.v:386-387). *)
Definition ext_but_NB (ly : alayout) : list (Z * Z) :=
  [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_F ly, kFakeStackSize);
   (ly_C ly, 256); (ly_D ly, 4096);
   (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly]
  ++ (if ly_SB ly =? 0 then [] else [(ly_SB ly, kStoreBlockSize)]).

(* Cell offsets in StackDepotBase (as_depot B, YG0f.v:240-241): nodes = TwoLevelMap {mu_ (StaticSpinMutex byte, the
   lock word's other bytes padding) at d_map1 - 8; map1_[] at d_map1}. *)
Definition tlm_mu : Z := d_map1 - 8.

Section kd.
(* PLACEHOLDER: the first Put's layout growth, a new
   relation beside today's layout_le (which stays as is). YD3j's kd_inst instantiates both with layout_grow / layout_grow_NB (YG0f.v:99, :105).
   Satisfiable: layout_grow_kd := fun _ _ => True. *)
Variable layout_grow_kd : alayout -> alayout -> Prop.
Hypothesis kd_grow_NB : forall ly nb, ly_NB ly = 0 -> layout_grow_kd ly (set_ly_NB ly nb).

(* Create's frame (0x71714 addi sp,sp,-32) above MmapOrDie's touched bytes (YD3h's MOD_STK). *)
Definition TLM_STK : Z := 32 + MOD_STK.

(* TwoLevelMap::Create(&theDepot.nodes, 0) on the first-use path (called from Put 0x7118c with id 1, idx = 1 >> 16 = 0).
   PRE: the cells Create reads (map1_[0] = 0, the lock word 0), the callee's cells (mod_cells; Create also reads the
   page-size GOT and cache at 0x71774), the stack window [sp - TLM_STK, sp), room and budget for the grant (mod_room,
   2 * n), that the model takes every extent the new block must avoid and the image, and the ledger's al_top;
   ly_NB ly = 0 (the "nodes block not yet mapped" sentinel, HELD). POST, normal exit, [exists x] (the mmap result):
   W the world grows by exactly X (allow_expose); P1 return x, cellX (map1_[0]) = x; P2 placement; P3 fresh; P4 zero
   and present in W', and taken in the model after; P5 frame: memory unchanged outside X, cellX, the lock word and the
   stack window, the lock word back to 0 (tab[b] and n_uniq_ids, which Put set before the call, untouched, by the
   frame); P6 the layout step (placeholder, HELD); P7 X disjoint from every vm_maps entry of md. No kernel ARm (see the
   header); no refused arm. *)
Definition tfib_tlm_create_nb_spec (B : asyms) : Prop :=
  forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte)
         (md : Model),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs in let DP := as_depot B in
  ly_NB ly = 0 ->
  getr regs 10 = Z_to_bv 64 (DP + tlm_mu) -> getr regs 11 = Z_to_bv 64 0 -> YK0s.ret_ok (getr regs 1) ->
  val_mem tfibsegs m (DP + d_map1) 8 0 -> val_mem tfibsegs m (DP + tlm_mu) 4 0 ->
  mod_cells m -> mod_room W md kNodesBlockSize ->
  sp mod 16 = 0 -> kHighMemBeg <= ly_stk_lo ly -> ly_stk_lo ly <= sp - TLM_STK -> sp <= ly_stk_hi ly ->
  (forall a, sp - TLM_STK <= a < sp -> apresent H mem a) ->
  Forall (md_takes md) (ext_but_NB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) ->
  (forall a, aclient_byte B ly S a -> md_takes md (a, 1)) ->
  md_takes md (TFIB_IMG_LO, TFIB_IMG_END - TFIB_IMG_LO) ->
  YM05.ceil_of_top (alloc_top (m_vmmaps md)) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_TwoLevelMap_Create_71714) mem (seg_rom tfibsegs)) md)
    (fun W' c' => exists x regs' mem' md',
      let m' := mrestrict (w_H W') mem' in
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
      (* W *)  w_A W' = (x, x + kNodesBlockSize) :: w_A W /\
               (forall a : word, ~ (x <= bv_unsigned a < x + kNodesBlockSize) -> w_H W' a = w_H W a) /\
      (* P1 *) getr regs' 10 = Z_to_bv 64 x /\ regs_preserved regs regs' /\ val_mem tfibsegs m' (DP + d_map1) 8 x /\
      (* P2 *) YG0f.page_aligned x /\ in_app x kNodesBlockSize /\
      (* P3 *) Forall (zdisjoint (x, kNodesBlockSize)) (ext_but_NB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
               (forall a, aclient_byte B ly S a -> ~ in_zr a (x, kNodesBlockSize)) /\
      (* P4 *) (forall i, 0 <= i < kNodesBlockSize ->
                 apresent (w_H W') mem' (x + i) /\ aview tfibsegs (w_H W') mem' (x + i) = Some 0) /\
               md_takes md' (x, kNodesBlockSize) /\ (forall e, md_takes md e -> md_takes md' e) /\
               m_vmmaps md' = m_vmmaps (mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kNodesBlockSize) md) /\
               m_vm_lazy md' = m_vm_lazy md /\
      (* P5 *) (forall a : word, ~ (sp - TLM_STK <= bv_unsigned a < sp) -> ~ (x <= bv_unsigned a < x + kNodesBlockSize) ->
                 ~ (DP + d_map1 <= bv_unsigned a < DP + d_map1 + 8) -> ~ (DP + tlm_mu <= bv_unsigned a < DP + tlm_mu + 4) ->
                 mem' a = mem a) /\
               val_mem tfibsegs m' (DP + tlm_mu) 4 0 /\
               (forall a, apresent H mem a -> apresent (w_H W') mem' a) /\ same_io md md' /\
      (* P6 *) layout_grow_kd ly (set_ly_NB ly x) /\
      (* P7 *) Forall (fun q => zdisjoint (x, kNodesBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps (m_vmmaps md))).
(* YD3h.v:50 md_takes md ((sp - 32) - MOD_STK, MOD_STK): from YD3g.v:100 (md_takes over ext_but_NB's stack extent, YD3g.v:63) and YD3g.v:98 (ly_stk_lo ly <= sp - TLM_STK, sp <= ly_stk_hi ly), by md_takes_sub. *)
(* YD3h.v:49 TFIB_IMG_END <= (sp - 32) - MOD_STK: TFIB_IMG_END = IMG_TOP = 0x5f3000 (YF0x.v:27; YImgTop.v:5) < kHighMemBeg <= ly_stk_lo ly <= sp - TLM_STK (YD3g.v:98). *)

(* ---- The walk. Phase A: 0x71714 to MmapOrDie's entry (the run stops at the fetch of 0x64278, which tfibtbl_rtB does
   not cover); the call: YD3h's mod_holds through SRr_bind; phase B: 0x717b8 to the ret at 0x717dc. ---- *)

Definition MUv : Z := 0x580460.
Definition CXv : Z := 0x580468.
Definition R_CS0 : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition R_MU0 : YP09.region := YP09.mkRegion None MUv (MUv + 4) MUv (MUv + 4) [YP09.mkChunk MUv (CVal 4 (SLit 0))].
Definition R_CX0 : YP09.region := YP09.mkRegion None CXv (CXv + 8) CXv (CXv + 8) [YP09.mkChunk CXv (CVal 8 (SLit 0))].
Definition R_GOT : YP09.region := YP09.mkRegion None MOD_PSC_GOT (MOD_PSC_GOT + 8) 0 0 [YP09.mkChunk MOD_PSC_GOT (CVal 8 (SLit MOD_PSC))].
Definition R_PSC : YP09.region := YP09.mkRegion None MOD_PSC (MOD_PSC + 8) 0 0 [YP09.mkChunk MOD_PSC (CVal 8 (SLit 4096))].
Definition CMEM0 : smem := [R_CS0; R_MU0; R_CX0; R_GOT; R_PSC].
Definition CREGS0 : list sv := sr_set (sr_set sr_atoms 10%bv (SLit MUv)) 11%bv (SLit 0).
Definition CF0 : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + 32) (2 ^ 64 - 1) 4)] [] [].
Definition SS_C0 : sstate := mkSS tfib_A_TwoLevelMap_Create_71714 CREGS0 CMEM0 None CF0.
Definition R_CS1 : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 32
  [YP09.mkChunk 0 (CVal 8 (SOff 36 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
   YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
Definition R_MU1 : YP09.region := YP09.mkRegion None MUv (MUv + 1) MUv (MUv + 1) [].
Definition R_CX1 : YP09.region := YP09.mkRegion None CXv (CXv + 8) CXv (CXv + 8) [].
Definition CMEM1 : smem := [R_CS1; R_MU1; R_CX1].
Definition CREGS1 : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 32 0)) 8%bv (SLit MUv)) 9%bv (SLit MUv)) 18%bv (SLit MOD_PSC).
Definition CF1 : facts := mkFacts [(2%nat, mkAF kHighMemBeg (2 ^ 64 - 1) 4)] [] [].
Definition SS_C1 : sstate := mkSS 0x717b8 CREGS1 CMEM1 None CF1.

Lemma wvb_vmmaps : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma wvb_lazy : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma md_takes_wvb : forall l X m e, md_takes (with_vm_backing l X m) e <-> md_takes m e.
Proof. intros l X m e. unfold md_takes. rewrite wvb_vmmaps. tauto. Qed.
Lemma mod_room_wvb : forall W m X n, mod_room W m n -> mod_room W (with_vm_backing (m_vm_lazy m) X m) n.
Proof. intros W m X n [H1 H2]. unfold mod_room, md_room, eager_used in *. rewrite wvb_vmmaps, wvb_lazy. tauto. Qed.
Lemma same_io_wvb : forall l X m, same_io m (with_vm_backing l X m).
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

(* md_takes' second disjunct is page_floor (alloc_top) <= fst e (amendment 10): a page-aligned
   grant [x, x + n) below alloc_top ends at or below page_floor (alloc_top) (page_floor_ge, YM05.v:31). *)
Lemma takes_fresh : forall md x n e,
  md_takes md e ->
  Forall (fun q => zdisjoint (x, n) (bv_unsigned (fst q), bv_unsigned (snd q)))
         (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
  x + n <= alloc_top (m_vmmaps md) -> 0 < n -> x mod 4096 = 0 -> n mod 4096 = 0 -> zdisjoint (x, n) e.
Proof.
  intros md x n e [[Hpos Hcov] | Htop] HF Htop' Hn Hxa Hna; unfold zdisjoint; cbn [fst snd].
  - destruct (Z_le_gt_dec (x + n) (fst e)) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (fst e + snd e) x) as [L2|L2]; [right; exact L2|].
    exfalso. assert (Hb : in_zr (Z.max x (fst e)) e) by (unfold in_zr; lia).
    destruct (proj1 (Exists_exists _ _) (Hcov _ Hb)) as (q & Hq & Hqb).
    pose proof (proj1 (Forall_forall _ _) HF q Hq) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - left. assert (Ha : (x + n) mod 4096 = 0) by (rewrite Z.add_mod, Hxa, Hna by lia; reflexivity).
    pose proof (page_floor_ge (alloc_top (m_vmmaps md)) (x + n) Ha Htop'). lia.
Qed.

Lemma rw7 : forall (m : word -> option byte) a, 0x96000 <= a < YImgTop.IMG_TOP -> writable_at tfibsegs m a.
Proof.
  intros m a Ha. unfold YImgTop.IMG_TOP in Ha. unfold writable_at. rewrite <- tsegs_tfasegs. apply tfib_rw_window.
  rewrite unsigned_lit_small by lia. exact Ha.
Qed.
Lemma region_ok_rw : forall E (m : word -> option byte) a n, 0x96000 <= a -> a + n <= YImgTop.IMG_TOP -> 0 <= n ->
  region_ok tfibsegs E m (YP09.mkRegion None a (a + n) a (a + n) []).
Proof.
  intros E m a n Ha Hh Hn. pose proof Hh as Hh'. unfold YImgTop.IMG_TOP in Hh'. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply rw7. unfold YImgTop.IMG_TOP. lia.
Qed.
Lemma region_ok_rwlit : forall E (m : word -> option byte) a (w : N) v,
  val_mem tfibsegs m a (N.to_nat w) v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> 0x96000 <= a ->
  a + Z.of_N w <= YImgTop.IMG_TOP ->
  region_ok tfibsegs E m (YP09.mkRegion None a (a + Z.of_N w) a (a + Z.of_N w) [YP09.mkChunk a (CVal w (SLit v))]).
Proof.
  intros E m a w v Hv Hr Hw Ha Hh. pose proof Hh as Hh'. unfold YImgTop.IMG_TOP in Hh'. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw7; unfold YImgTop.IMG_TOP; lia|].
  apply Forall_cons; [|apply Forall_nil].
  eapply chunk_ok_val; [reflexivity | exact Hr | exact Hw | rewrite Z.add_0_l; exact Hv].
Qed.
Lemma AFo7 : forall E k X lo hi al, ew E k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 ->
  0 <= al <= 64 -> afact_ok E k (mkAF lo hi al).
Proof. intros E k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE.
  rewrite unsigned_lit_small by exact HX. repeat split; lia. Qed.
Lemma wr_C0 : forall E a, in_wrange E CMEM0 a ->
  (bv_unsigned (ew E 2) - 32 <= a < bv_unsigned (ew E 2)) \/ (MUv <= a < MUv + 4) \/ (CXv <= a < CXv + 8).
Proof.
  intros E a (r & Hin & Hr). unfold CMEM0 in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbn [R_CS0 R_MU0 R_CX0 R_GOT R_PSC YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Lemma wr_C1 : forall E a, in_wrange E CMEM1 a ->
  (bv_unsigned (ew E 2) <= a < bv_unsigned (ew E 2) + 32) \/ (MUv <= a < MUv + 1) \/ (CXv <= a < CXv + 8).
Proof.
  intros E a (r & Hin & Hr). unfold CMEM1 in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [R_CS1 R_MU1 R_CX1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Ltac rreg7 HS r R :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  pose proof (st_ok_reg_denot H E ss ms r HS) as R; change (sr_get (ss_regs ss) r) with e in R end.
Ltac cs7 := unfold callee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end;
  lia.
Lemma soff0 : forall E k, sv_denot E (SOff k 0) = ew E k.
Proof. intros E k. apply bv_eq. rewrite denot_SOff. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. apply u64_range. Qed.
Lemma rp_at : forall (rg rg' : bvmap 5 word) (r : bv 5), regs_preserved rg rg' -> callee_saved (bv_unsigned r) ->
  getr rg' r = getr rg r.
Proof. intros rg rg' r H Hc. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H. exact Hc. Qed.
Lemma region_ok_stk4 : forall E (m : word -> option byte) (b v0 v1 v2 v3 : Z),
  bv_unsigned (ew E 2) = b -> 0 <= b -> b + 32 <= 2 ^ 64 ->
  (forall a, b <= a < b + 32 -> writable_at tfibsegs m a) ->
  bv_unsigned (ew E 36) = v0 -> bv_unsigned (ew E 35) = v1 -> bv_unsigned (ew E 34) = v2 -> bv_unsigned (ew E 33) = v3 ->
  val_mem tfibsegs m b 8 v0 -> val_mem tfibsegs m (b + 8) 8 v1 -> val_mem tfibsegs m (b + 16) 8 v2 -> val_mem tfibsegs m (b + 24) 8 v3 ->
  region_ok tfibsegs E m R_CS1.
Proof.
  intros E m b v0 v1 v2 v3 Hb Hb0 Hb1 Hw E36 E35 E34 E33 V0 V1 V2 V3. unfold region_ok, R_CS1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E m b 0 8%N (SOff 36 0) v0); [rewrite soff0, <- E36; symmetry; apply Z_to_bv_bv_unsigned | rewrite <- E36; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia | rewrite Z.add_0_r; exact V0].
  - apply (chunk_ok_val tfibsegs E m b 8 8%N (SOff 35 0) v1); [rewrite soff0, <- E35; symmetry; apply Z_to_bv_bv_unsigned | rewrite <- E35; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia | exact V1].
  - apply (chunk_ok_val tfibsegs E m b 16 8%N (SOff 34 0) v2); [rewrite soff0, <- E34; symmetry; apply Z_to_bv_bv_unsigned | rewrite <- E34; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia | exact V2].
  - apply (chunk_ok_val tfibsegs E m b 24 8%N (SOff 33 0) v3); [rewrite soff0, <- E33; symmetry; apply Z_to_bv_bv_unsigned | rewrite <- E33; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia | exact V3].
Qed.

Lemma mbyte_hsame : forall (H H' : word -> bool) (mem mem' : word -> option byte) a,
  H' (Z_to_bv 64 a) = H (Z_to_bv 64 a) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) ->
  mbyte tfibsegs (mrestrict H' mem') a = mbyte tfibsegs (mrestrict H mem) a.
Proof. intros H H' mem mem' a E1 E2. unfold mbyte, mrestrict. rewrite E1, E2. reflexivity. Qed.
Lemma val_mem_hframe : forall (H H' : word -> bool) (mem mem' : word -> option byte) a n v,
  (forall k, a <= k < a + Z.of_nat n -> H' (Z_to_bv 64 k) = H (Z_to_bv 64 k) /\ mem' (Z_to_bv 64 k) = mem (Z_to_bv 64 k)) ->
  val_mem tfibsegs (mrestrict H mem) a n v -> val_mem tfibsegs (mrestrict H' mem') a n v.
Proof.
  intros H H' mem mem' a n v Hfr Hv. unfold val_mem in *. intros k Hk. specialize (Hv k Hk).
  destruct (Hfr (a + Z.of_nat k) ltac:(lia)) as [E1 E2]. rewrite (mbyte_hsame H H' mem mem' _ E1 E2). exact Hv.
Qed.
Lemma md_takes_sub : forall md lo n lo' n', md_takes md (lo, n) -> lo <= lo' -> lo' + n' <= lo + n -> 0 < n' ->
  md_takes md (lo', n').
Proof.
  intros md lo n lo' n' [[Hp Hc] | Ht] H1 H2 H3; unfold md_takes; cbn [fst snd] in *.
  - left. split; [exact H3|]. intros a Ha. apply Hc. unfold in_zr in *. cbn [fst snd] in *. lia.
  - right. lia.
Qed.
Lemma mmap_model_vmmaps_wvb : forall a n l X m, m_vmmaps (mmap_model a n (with_vm_backing l X m)) = m_vmmaps (mmap_model a n m).
Proof. intros a n l X [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Theorem tfib_tlm_create_nb_ok : forall B, TfibSyms B -> tfib_tlm_create_nb_spec B.
Proof using kd_grow_NB.
  intros B HB W ly S regs mem md. cbv zeta.
  intros HNB R10 R11 Hra VCX VMU HMC HRM Hsp16 Hstk0 Hsplo Hsphi Pstk HTK HCL HIMG HCEIL.
  pose proof (ts_depot B HB) as EDP. rewrite EDP in *.
  assert (EMU : TFIB_DEPOT + tlm_mu = MUv) by reflexivity. assert (ECX : TFIB_DEPOT + d_map1 = CXv) by reflexivity.
  rewrite EMU, ECX in *.
  set (sp := spZ regs) in *. unfold TLM_STK, MOD_STK in *.
  pose proof (u64_range (getr regs 2)) as SPR. fold (spZ regs) in SPR. fold sp in SPR.
  assert (SPLO : kHighMemBeg + 32 <= sp) by lia.
  assert (SPL : 0x10007fff8000 + 32 <= sp) by (unfold kHighMemBeg in SPLO; lia).
  assert (SPL2 : 0x10007fff8000 <= sp - (32 + 104)) by (pose proof Hstk0 as K0; unfold kHighMemBeg in K0; lia).
  set (E0 := Ereg regs []).
  assert (E02 : ew E0 2 = getr regs 2) by exact (ew_Ereg_nat regs [] 2 2%bv eq_refl).
  assert (U02 : bv_unsigned (ew E0 2) = sp) by (rewrite E02; reflexivity).
  (* the seed *)
  assert (HS0 : st_ok tfibsegs E0 SS_C0 (restrict (w_H W) (mkst regs (Z_to_bv 64 tfib_A_TwoLevelMap_Create_71714) mem (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold SS_C0, CREGS0. apply (entry_st_ok_full tfibsegs).
    - apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact R11].
      apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact R10].
    - vm_compute. reflexivity.
    - unfold CMEM0. destruct HMC as (MC1 & MC2 & _).
      apply Forall_cons. { apply (region_ok_stack tfibsegs E0 _ 2 sp (-32)); [exact U02 | lia | lia |].
        intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, YImgTop.IMG_TOP; lia | apply Pstk; lia]. }
      apply Forall_cons. { apply (region_ok_rwlit E0 _ MUv 4 0); [exact VMU | cbn; lia | cbn; lia | unfold MUv; lia | unfold MUv, YImgTop.IMG_TOP; cbn; lia]. }
      apply Forall_cons. { apply (region_ok_rwlit E0 _ CXv 8 0); [exact VCX | cbn; lia | cbn; lia | unfold CXv; lia | unfold CXv, YImgTop.IMG_TOP; cbn; lia]. }
      apply Forall_cons. { apply (region_ok_lit E0 _ MOD_PSC_GOT 8 MOD_PSC); [exact MC1 | unfold MOD_PSC; cbn; lia | cbn; lia | unfold MOD_PSC_GOT; lia | unfold MOD_PSC_GOT; cbn; lia]. }
      apply Forall_cons. { apply (region_ok_lit E0 _ MOD_PSC 8 4096); [exact MC2 | cbn; lia | cbn; lia | unfold MOD_PSC; lia | unfold MOD_PSC; cbn; lia]. }
      apply Forall_nil.
    - apply pairwise_disjoint_of_extents. unfold CMEM0, R_CS0, R_MU0, R_CX0, R_GOT, R_PSC, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0. rewrite U02.
      unfold MUv, CXv, MOD_PSC_GOT, MOD_PSC. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - split; [| split; exact I]. cbn [CF0 f_atoms atoms_ok]. split; [| exact I].
      assert (E2' : ew E0 2 = Z_to_bv 64 sp) by (rewrite E02; symmetry; apply Z_to_bv_bv_unsigned).
      apply (AFo7 E0 2%nat sp _ _ _ E2'); [exact SPR | lia | change (2 ^ 4) with 16; exact Hsp16 | lia]. }
  pose proof Hwx_tfa as HWX.
  srr_runG tfibtbl_rtB_ok HS0.
  (* at MmapOrDie's entry: the run stopped at the fetch of 0x64278 *)
  change (ss_mem SS_C0) with CMEM0 in HF.
  lazymatch type of HS0 with st_ok _ _ ?ssA _ => set (sA := ssA) in HS0 end.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 sA ms HS0 eq_refl) as SH1.
  rreg7 HS0 (1%bv : bv 5) G1. rreg7 HS0 (2%bv : bv 5) G2. rreg7 HS0 (10%bv : bv 5) G10. rreg7 HS0 (11%bv : bv 5) G11.
  rreg7 HS0 (8%bv : bv 5) G8. rreg7 HS0 (9%bv : bv 5) G9. rreg7 HS0 (18%bv : bv 5) G18.
  cbn [sv_denot] in G1, G10, G11, G8, G9, G18.
  assert (U12 : bv_unsigned (getr (ms_regs ms) 2) = sp - 32).
  { rewrite G2, denot_SOff, U02. unfold zcanon, M64. apply Z.mod_small. lia. }
  assert (A1 : argZ (ms_regs ms) 0 = kNodesBlockSize).
  { unfold argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10. reflexivity. }
  assert (A4 : argZ (ms_regs ms) 1 <> 0).
  { unfold argZ. replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G11. cbn. discriminate. }
  assert (A6 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (FR1 : forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> ~ (MUv <= bv_unsigned x < MUv + 4) ->
    ~ (CXv <= bv_unsigned x < CXv + 8) -> ms_mem ms x = mem x).
  { intros x N1 N2 N3. apply HF. intros Hw. destruct (wr_C0 E0 _ Hw) as [X|[X|X]]; [rewrite U02 in X|..]; tauto. }
  assert (A7 : mod_cells (mrestrict (w_H W) (ms_mem ms))).
  { destruct HMC as (MC1 & MC2 & MC3 & (f & MC4 & MC5) & MC6).
    assert (K : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 0x580460 -> val_mem tfibsegs (mrestrict (w_H W) mem) a n v ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a n v).
    { intros a n v Ha Hn Hv. apply (val_mem_hframe (w_H W) (w_H W) mem (ms_mem ms)); [| exact Hv]. intros k Hk. split; [reflexivity|].
      apply FR1; rewrite unsigned_lit_small by lia; unfold MUv, CXv; lia. }
    unfold mod_cells. unfold MOD_PSC_GOT, MOD_PSC, MOD_CF_GOT, MOD_CF in *.
    split; [apply K; [lia | cbn; lia | exact MC1]|]. split; [apply K; [lia | cbn; lia | exact MC2]|].
    split; [apply K; [lia | cbn; lia | exact MC3]|]. split; [exists f; split; [apply K; [lia | cbn; lia | exact MC4] | exact MC5]|].
    apply K; [lia | cbn; lia | exact MC6]. }
  assert (A8 : mod_room W (with_vm_backing (m_vm_lazy md) mat md) kNodesBlockSize) by (apply mod_room_wvb; exact HRM).
  assert (A9 : spZ (ms_regs ms) mod 16 = 0).
  { unfold spZ. rewrite U12. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact Hsp16. }
  assert (ATOP : TFIB_IMG_END <= spZ (ms_regs ms) - MOD_STK).
  { unfold spZ. rewrite U12. unfold MOD_STK, TFIB_IMG_END, YImgTop.IMG_TOP. lia. }
  assert (A10 : forall a, spZ (ms_regs ms) - MOD_STK <= a < spZ (ms_regs ms) -> apresent (w_H W) (ms_mem ms) a).
  { intros a Ha. unfold spZ, MOD_STK in Ha. rewrite U12 in Ha. apply (apresent_grows (w_H W) mem); [exact HG | apply Pstk; lia]. }
  assert (ASTK : md_takes (with_vm_backing (m_vm_lazy md) mat md) (spZ (ms_regs ms) - MOD_STK, MOD_STK)).
  { apply md_takes_wvb. unfold spZ. rewrite U12.
    apply (md_takes_sub md (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)); [| unfold MOD_STK; lia | unfold MOD_STK; lia | unfold MOD_STK; lia].
    apply (proj1 (Forall_forall _ _) HTK). apply in_or_app. left. unfold ext_but_NB. apply in_or_app. left. cbn; tauto. }
  assert (AIMG : md_takes (with_vm_backing (m_vm_lazy md) mat md) (TFIB_IMG_LO, TFIB_IMG_END - TFIB_IMG_LO))
    by (apply md_takes_wvb; exact HIMG).
  (* phase A's memory and the registers it leaves *)
  assert (CH : forall (i j : nat) off (n : N) e v a, nth_error (ss_mem sA) i = Some (nth i (ss_mem sA) R_CS0) ->
    nth_error (YP09.r_chunks (nth i (ss_mem sA) R_CS0)) j = Some (YP09.mkChunk off (CVal n e)) ->
    a = base_val E0 (YP09.r_base (nth i (ss_mem sA) R_CS0)) + off -> sv_denot E0 e = Z_to_bv 64 v ->
    0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a (N.to_nat n) v).
  { intros i j off n e v a Hi Hj Ha He Hv Hn. eapply (chunk_val_at (w_H W) E0 sA ms i j); eassumption. }
  assert (EA : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r)
    by (intros k r Hk; exact (ew_Ereg_nat regs [] k r Hk)).
  assert (B0 : base_val E0 (YP09.r_base (nth 0 (ss_mem sA) R_CS0)) = sp) by (change (YP09.r_base (nth 0 (ss_mem sA) R_CS0)) with (Some 2%nat); exact U02).
  assert (B1 : base_val E0 (YP09.r_base (nth 1 (ss_mem sA) R_CS0)) = 0) by (change (YP09.r_base (nth 1 (ss_mem sA) R_CS0)) with (@None nat); reflexivity).
  assert (VS0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp - 32) 8 (bv_unsigned (getr regs 18%bv))).
  { apply (CH 0%nat 0%nat (-32) 8%N (SOff 18 0)); [reflexivity | reflexivity | rewrite B0; lia
    | rewrite soff0, (EA 18%nat 18%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia]. }
  assert (VS1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp - 24) 8 (bv_unsigned (getr regs 9%bv))).
  { apply (CH 0%nat 1%nat (-24) 8%N (SOff 9 0)); [reflexivity | reflexivity | rewrite B0; lia
    | rewrite soff0, (EA 9%nat 9%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia]. }
  assert (VS2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp - 16) 8 (bv_unsigned (getr regs 8%bv))).
  { apply (CH 0%nat 2%nat (-16) 8%N (SOff 8 0)); [reflexivity | reflexivity | rewrite B0; lia
    | rewrite soff0, (EA 8%nat 8%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia]. }
  assert (VS3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp - 8) 8 (bv_unsigned (getr regs 1%bv))).
  { apply (CH 0%nat 3%nat (-8) 8%N (SOff 1 0)); [reflexivity | reflexivity | rewrite B0; lia
    | rewrite soff0, (EA 1%nat 1%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range | cbn; lia]. }
  assert (VM1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) MUv 4 1).
  { apply (CH 1%nat 0%nat MUv 4%N (SLit 1)); [reflexivity | reflexivity | rewrite B1; lia | reflexivity | cbn; lia | cbn; lia]. }
  assert (GA : forall (r : bv 5), sr_get (ss_regs sA) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (st_ok_reg_denot (w_H W) E0 sA ms r HS0), Hr, soff0. apply EA.
    rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range 5 r); lia). reflexivity. }
  rewrite SH1.
  eapply SRr_bind; [exact (mod_holds W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) kNodesBlockSize
    A1 ltac:(unfold kNodesBlockSize; lia) ltac:(unfold YG0f.page_aligned, kNodesBlockSize; reflexivity)
    A4 A6 A7 A8 A9 ATOP A10 ASTK AIMG) |].
  (* back from MmapOrDie at 0x717b8 *)
  intros W2 c2 Hle2 (x & regs2 & mem2 & md2 & Ec2 & WA2 & WH2 & X10 & RP2 & XAL & XPOS & XGR & XFR & XTOP & XZ & XTK & XMONO
    & (mat2 & XMD) & XFRM & XPR & XIO).
  subst c2. rewrite G1. unfold MOD_STK in XFRM.
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CEIL.
  (* P2: in_app from the model, as in anon_grant_facts (YG0j.v:306-325) *)
  assert (DB : Forall (zdisjoint (x, kNodesBlockSize)) band_maps).
  { apply Forall_forall. intros e He. apply (takes_fresh (with_vm_backing (m_vm_lazy md) mat md)); [| exact XFR | exact XTOP | unfold kNodesBlockSize; lia | exact XAL | reflexivity].
    apply md_takes_wvb. apply (proj1 (Forall_forall _ _) HTK). rewrite !in_app_iff. right; right; right. exact He. }
  assert (XCE : x + kNodesBlockSize <= ASAN_CEIL).
  { unfold ASAN_CEIL. apply (YM05.grant_below_ceil (alloc_top (m_vmmaps (with_vm_backing (m_vm_lazy md) mat md))) (x + kNodesBlockSize));
      [rewrite wvb_vmmaps; exact HCEIL | | exact XTOP].
    unfold YG0f.page_aligned in XAL. unfold kNodesBlockSize. rewrite Z.add_mod by lia. rewrite XAL. reflexivity. }
  assert (XAPP : in_app x kNodesBlockSize).
  { pose proof DB as B'. unfold band_maps in B'. apply Forall_cons_iff in B' as [D1 B']. apply Forall_cons_iff in B' as [D2 B'].
    apply Forall_cons_iff in B' as [D3 _]. unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3. unfold in_app.
    unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kNodesBlockSize in *.
    split; [| clear - D1 D2 D3 XCE CEIL; lia].
    unfold YG0f.page_aligned in XAL. apply Z.mod_divide in XAL as [q Hq]; [|lia]. lia. }
  assert (XR : 4096 <= x /\ x + kNodesBlockSize <= 0x7fffff800000).
  { destruct XAPP as [XA1 [XA2 | [_ XA2]]]; unfold kLowShadowBeg in *; lia. }
  assert (DSTK : zdisjoint (x, kNodesBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
  { apply (takes_fresh (with_vm_backing (m_vm_lazy md) mat md)); [| exact XFR | exact XTOP | unfold kNodesBlockSize; lia | exact XAL | reflexivity].
    apply md_takes_wvb. apply (proj1 (Forall_forall _ _) HTK). apply in_or_app. left. unfold ext_but_NB. apply in_or_app. left. cbn; tauto. }
  assert (DIMG : zdisjoint (x, kNodesBlockSize) (TFIB_IMG_LO, TFIB_IMG_END - TFIB_IMG_LO)).
  { apply (takes_fresh (with_vm_backing (m_vm_lazy md) mat md)); [exact AIMG | exact XFR | exact XTOP | unfold kNodesBlockSize; lia | exact XAL | reflexivity]. }
  unfold zdisjoint in DSTK, DIMG. cbn [fst snd] in DSTK, DIMG. unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in DIMG.
  assert (FR2 : forall a : word, ~ (sp - 32 - 104 <= bv_unsigned a < sp - 32) -> ~ (x <= bv_unsigned a < x + kNodesBlockSize) ->
    mem2 a = ms_mem ms a).
  { intros a N1 N2. apply XFRM; [unfold spZ; rewrite U12; exact N1 | exact N2]. }
  set (E1 := Ereg regs2 [Z_to_bv 64 x; getr regs 1%bv; getr regs 8%bv; getr regs 9%bv; getr regs 18%bv]).
  assert (RQ : forall r : bv 5, callee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r Hr; exact (rp_at _ _ r RP2 Hr)).
  assert (E1r : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E1 k = getr regs2 r)
    by (intros k r Hk; exact (ew_Ereg_nat regs2 _ k r Hk)).
  assert (E12 : bv_unsigned (ew E1 2) = sp - 32).
  { rewrite (E1r 2%nat 2%bv eq_refl), (RQ 2%bv ltac:(cs7)). exact U12. }
  assert (STK2 : forall a, sp - 32 <= a < sp -> mem2 (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
  { intros a Ha. apply FR2; rewrite unsigned_lit_small by lia; [lia|]. unfold kNodesBlockSize in *. lia. }
  assert (HSTK2 : forall a, sp - 32 <= a < sp -> w_H W2 (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a)).
  { intros a Ha. apply WH2. rewrite unsigned_lit_small by lia. unfold kNodesBlockSize in *. lia. }
  assert (VF2 : forall a n v, sp - 32 <= a -> a + Z.of_nat n <= sp -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a n v ->
    val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v).
  { intros a n v H1 H2 Hv. apply (val_mem_hframe (w_H W) (w_H W2) (ms_mem ms) mem2); [| exact Hv].
    intros k Hk. split; [apply HSTK2; lia | apply STK2; lia]. }
  assert (HS1 : st_ok tfibsegs E1 SS_C1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 464824) mem2 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold SS_C1, CREGS1. change 464824 with 0x717b8. apply (entry_st_ok_full tfibsegs).
    - apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; rewrite (RQ 18%bv ltac:(cs7)); exact G18].
      apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; rewrite (RQ 9%bv ltac:(cs7)); exact G9].
      apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; rewrite (RQ 8%bv ltac:(cs7)); exact G8].
      apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | rewrite soff0; exact X10].
    - vm_compute. reflexivity.
    - unfold CMEM1. apply Forall_cons.
      { apply (region_ok_stk4 E1 _ (sp - 32) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 9%bv))
          (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 1%bv))); [fold E1; exact E12 | lia | lia | | reflexivity | reflexivity | reflexivity | reflexivity
          | apply VF2; [lia | cbn; lia | exact VS0] | apply VF2; [lia | cbn; lia | replace (sp - 32 + 8) with (sp - 24) by lia; exact VS1]
          | apply VF2; [lia | cbn; lia | replace (sp - 32 + 16) with (sp - 16) by lia; exact VS2]
          | apply VF2; [lia | cbn; lia | replace (sp - 32 + 24) with (sp - 8) by lia; exact VS3]].
        intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, YImgTop.IMG_TOP; lia|].
        apply XPR. apply (apresent_grows (w_H W) mem); [exact HG | apply Pstk; lia]. }
      apply Forall_cons. { apply (region_ok_rw E1 _ MUv 1); unfold MUv, YImgTop.IMG_TOP; lia. }
      apply Forall_cons. { apply (region_ok_rw E1 _ CXv 8); unfold CXv, YImgTop.IMG_TOP; lia. }
      apply Forall_nil.
    - apply pairwise_disjoint_of_extents. unfold CMEM1, R_CS1, R_MU1, R_CX1, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E1. rewrite E12.
      unfold MUv, CXv. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [| split; exact I]. cbn [CF1 f_atoms atoms_ok]. split; [| exact I].
      assert (E2' : ew E1 2 = Z_to_bv 64 (sp - 32)) by (rewrite <- E12; symmetry; apply Z_to_bv_bv_unsigned).
      apply (AFo7 E1 2%nat (sp - 32) _ _ _ E2'); [lia | unfold kHighMemBeg; lia | | lia].
      change (2 ^ 4) with 16. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact Hsp16. }
  srr_runG tfibtbl_rtB_ok HS1.
  (* at the ret 0x717dc *)
  lazymatch goal with HFx : frame_of E1 _ mem2 (ms_mem ?m3), HGx : mem_grows _ (mrestrict _ (ms_mem ?m3)) |- _ =>
    rename m3 into ms3; rename HFx into HF3; rename HGx into HG3 end.
  change (ss_mem SS_C1) with CMEM1 in HF3.
  lazymatch type of HS1 with st_ok _ _ ?ssB _ => set (sB := ssB) in HS1 end.
  rreg7 HS1 (1%bv : bv 5) H1. rreg7 HS1 (2%bv : bv 5) H2. rreg7 HS1 (10%bv : bv 5) H10.
  rreg7 HS1 (8%bv : bv 5) H8. rreg7 HS1 (9%bv : bv 5) H9. rreg7 HS1 (18%bv : bv 5) H18.
  rewrite soff0 in H1, H10, H8, H9, H18.
  assert (FR3 : forall y : word, ~ (sp - 32 <= bv_unsigned y < sp) -> ~ (MUv <= bv_unsigned y < MUv + 1) ->
    ~ (CXv <= bv_unsigned y < CXv + 8) -> ms_mem ms3 y = mem2 y).
  { intros y N1 N2 N3. apply HF3. intros Hw. destruct (wr_C1 E1 _ Hw) as [X|[X|X]]; [rewrite E12 in X; lia | tauto | tauto]. }
  assert (XU : 0 <= x /\ x + kNodesBlockSize < 2 ^ 64) by (unfold kNodesBlockSize in *; lia).
  assert (KS : kNodesBlockSize = 0x100000) by reflexivity.
  eapply (SRr_ret_at tfibsegs tfibtbl_rtB tfibtbl_rtB_ok HWX W2 E1 sB ms3 _ _ HS1 eq_refl); [vm_compute; reflexivity |].
  intros mat1. rewrite ?wvb_collapse. cbv beta.
  exists x, (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md2) mat1 md2).
  split.
  { rewrite H1. change (ew E1 33) with (getr regs 1%bv). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [exact WA2|]. split; [exact WH2|].
  split. { rewrite H10. reflexivity. }
  split.
  { apply regs_preserved_intro.
    - apply bv_eq. rewrite H2, denot_SOff, E12. change (bv_unsigned (getr regs 2%bv)) with sp. unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
    - rreg7 HS1 (3%bv : bv 5) H3. rewrite H3, soff0, (E1r 3%nat 3%bv eq_refl), (RQ 3%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (4%bv : bv 5) H4. rewrite H4, soff0, (E1r 4%nat 4%bv eq_refl), (RQ 4%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rewrite H8. reflexivity.
    - rewrite H9. reflexivity.
    - rewrite H18. reflexivity.
    - rreg7 HS1 (19%bv : bv 5) H19. rewrite H19, soff0, (E1r 19%nat 19%bv eq_refl), (RQ 19%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (20%bv : bv 5) H20. rewrite H20, soff0, (E1r 20%nat 20%bv eq_refl), (RQ 20%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (21%bv : bv 5) H21. rewrite H21, soff0, (E1r 21%nat 21%bv eq_refl), (RQ 21%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (22%bv : bv 5) H22. rewrite H22, soff0, (E1r 22%nat 22%bv eq_refl), (RQ 22%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (23%bv : bv 5) H23. rewrite H23, soff0, (E1r 23%nat 23%bv eq_refl), (RQ 23%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (24%bv : bv 5) H24. rewrite H24, soff0, (E1r 24%nat 24%bv eq_refl), (RQ 24%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (25%bv : bv 5) H25. rewrite H25, soff0, (E1r 25%nat 25%bv eq_refl), (RQ 25%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (26%bv : bv 5) H26. rewrite H26, soff0, (E1r 26%nat 26%bv eq_refl), (RQ 26%bv ltac:(cs7)). apply GA. vm_compute. reflexivity.
    - rreg7 HS1 (27%bv : bv 5) H27. rewrite H27, soff0, (E1r 27%nat 27%bv eq_refl), (RQ 27%bv ltac:(cs7)). apply GA. vm_compute. reflexivity. }
  split.
  { eapply (chunk_val_at (w_H W2) E1 sB ms3 2 0 _ CXv 8%N (SOff 32 0) x CXv); [exact HS1 | reflexivity | reflexivity
      | reflexivity | rewrite soff0; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]. }
  split; [exact XAL|]. split; [exact XAPP|].
  split.
  { apply Forall_forall. intros e He. apply (takes_fresh (with_vm_backing (m_vm_lazy md) mat md)); [| exact XFR | exact XTOP | lia | exact XAL | reflexivity].
    apply md_takes_wvb. exact (proj1 (Forall_forall _ _) HTK e He). }
  split.
  { intros a Ha Hin. pose proof (takes_fresh (with_vm_backing (m_vm_lazy md) mat md) x kNodesBlockSize (a, 1)
      (proj2 (md_takes_wvb _ _ _ _) (HCL a Ha)) XFR XTOP ltac:(lia) XAL eq_refl) as D.
    unfold zdisjoint, in_zr in D, Hin. cbn [fst snd] in D, Hin. lia. }
  assert (EQX : forall i, 0 <= i < kNodesBlockSize -> ms_mem ms3 (Z_to_bv 64 (x + i)) = mem2 (Z_to_bv 64 (x + i))).
  { intros i Hi. apply FR3; rewrite unsigned_lit_small by lia; unfold MUv, CXv in *; lia. }
  split.
  { intros i Hi. destruct (XZ i Hi) as [Pp Pv]. split.
    - apply (apresent_same _ mem2); [exact (EQX i Hi) | exact Pp].
    - rewrite (aview_same _ mem2 _ _ (EQX i Hi)). exact Pv. }
  split; [apply md_takes_wvb; exact XTK|].
  split; [intros e He; apply md_takes_wvb; apply XMONO; apply md_takes_wvb; exact He|].
  split. { rewrite wvb_vmmaps, XMD, wvb_vmmaps. apply mmap_model_vmmaps_wvb. }
  split. { rewrite wvb_lazy, XMD, !wvb_lazy; try reflexivity. }
  split.
  { intros a N1 N2 N3 N4. rewrite FR3 by lia. rewrite FR2 by lia. apply FR1; lia. }
  split.
  { assert (VB0 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms3)) MUv 1 0).
    { eapply (chunk_val_at (w_H W2) E1 sB ms3 1 0 _ MUv 1%N (SLit 0) 0 MUv); [exact HS1 | reflexivity | reflexivity
        | reflexivity | reflexivity | cbn; lia | cbn; lia]. }
    assert (EQM : forall k, 1 <= k < 4 -> ms_mem ms3 (Z_to_bv 64 (MUv + k)) = ms_mem ms (Z_to_bv 64 (MUv + k))).
    { intros k Hk. rewrite FR3 by (rewrite unsigned_lit_small by (unfold MUv; lia); unfold MUv, CXv in *; lia).
      apply FR2; rewrite unsigned_lit_small by (unfold MUv; lia); unfold MUv in *; lia. }
    assert (HQM : forall k, 1 <= k < 4 -> w_H W2 (Z_to_bv 64 (MUv + k)) = w_H W (Z_to_bv 64 (MUv + k))).
    { intros k Hk. apply WH2. rewrite unsigned_lit_small by (unfold MUv; lia). unfold MUv, kNodesBlockSize in *. lia. }
    intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
    - rewrite (VB0 0%nat ltac:(lia)). reflexivity.
    - rewrite (mbyte_hsame (w_H W) (w_H W2) (ms_mem ms) (ms_mem ms3) _ (HQM (Z.of_nat 1) ltac:(cbn; lia)) (EQM (Z.of_nat 1) ltac:(cbn; lia))), (VM1 1%nat ltac:(lia)). reflexivity.
    - rewrite (mbyte_hsame (w_H W) (w_H W2) (ms_mem ms) (ms_mem ms3) _ (HQM (Z.of_nat 2) ltac:(cbn; lia)) (EQM (Z.of_nat 2) ltac:(cbn; lia))), (VM1 2%nat ltac:(lia)). reflexivity.
    - rewrite (mbyte_hsame (w_H W) (w_H W2) (ms_mem ms) (ms_mem ms3) _ (HQM (Z.of_nat 3) ltac:(cbn; lia)) (EQM (Z.of_nat 3) ltac:(cbn; lia))), (VM1 3%nat ltac:(lia)). reflexivity. }
  split.
  { intros a Pa. apply (apresent_grows (w_H W2) mem2); [exact HG3|]. apply XPR. apply (apresent_grows (w_H W) mem); [exact HG | exact Pa]. }
  split.
  { pose proof (same_io_wvb (m_vm_lazy md) mat md) as I1. pose proof (same_io_wvb (m_vm_lazy md2) mat1 md2) as I3.
    unfold same_io in *. destruct I1 as (I1a & I1b & I1c & I1d). destruct XIO as (I2a & I2b & I2c & I2d).
    destruct I3 as (I3a & I3b & I3c & I3d). repeat split; congruence. }
  split; [exact (kd_grow_NB ly x HNB)|].
  rewrite wvb_vmmaps in XFR. apply Forall_app in XFR. exact (proj2 XFR).
Qed.
End kd.
End g.
