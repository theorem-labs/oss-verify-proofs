(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_SHBASE : Z := 0x112a80. (* [comment removed for export] *)
Definition AGOT_SUAR : Z := 0x112ad8.   (* [comment removed for export] *)
Definition ASUAR : Z := 0x11b680.       (* [comment removed for export] *)
Definition AMEMCPY : Z := 0x6584c.      (* [comment removed for export] *)
Definition ASTKMALLOC2U : Z := 0x50270.  (* [comment removed for export] *)
Definition ASTKMALLOC4 : Z := 0x5040c.  (* [comment removed for export] *)
Definition ASTKMALLOC5 : Z := 0x505d8.  (* [comment removed for export] *)
Definition ASTKFREE5 : Z := 0x507e4.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AVTAB_IMPL : Z := 0x10f610.
Definition vtab_impl_cells : list cell :=
  [C8 (Z_to_bv 64 0xcaf00); C8 (Z_to_bv 64 0xcb0a0); C8 (Z_to_bv 64 0xcb240); C8 (Z_to_bv 64 0x973c0); C8 (Z_to_bv 64 0x9a500); C8 (Z_to_bv 64 0x9a6e8)].
(* [comment removed for export] *)
Definition AVTAB_DOM : Z := 0x10f6d0.
Definition vtab_dom_cells : list cell :=
  [C8 (Z_to_bv 64 0xcaeac); C8 (Z_to_bv 64 0x97660); C8 (Z_to_bv 64 0x9ab3c); C8 (Z_to_bv 64 0xb2524); C8 (Z_to_bv 64 0xc9dbc);
   C8 (Z_to_bv 64 0xca660); C8 (Z_to_bv 64 0xcb288); C8 (Z_to_bv 64 0xcb3fc); C8 (Z_to_bv 64 0xcb570); C8 (Z_to_bv 64 0xcb65c)].

Definition AMEMCPY_STACK : Z := 2224.
Definition SM4_STACK : Z := 4096.
Definition SM5_STACK : Z := 4096.

(* [comment removed for export] *)
Definition AREAL_MC : Z := 0x114860.   (* [comment removed for export] *)
Definition AMCFLAGS : Z := 0x1ad2a0.   (* [comment removed for export] *)
Definition AFMIN : Z := 0x1174c0.      (* [comment removed for export] *)
Definition ABOM : Z := 0x22f40.        (* [comment removed for export] *)
Definition ACTAB : Z := 0x27e00.       (* [comment removed for export] *)
Definition rt_real_mc (m : amem) : Prop := rw_cells bsegs m AREAL_MC [C8 (Z_to_bv 64 0x108868); C8 (Z_to_bv 64 0x108798)].
Definition rt_flags (m : amem) : Prop := rw_cells bsegs m AMCFLAGS [C8 (Z_to_bv 64 72340172838076673)].
Lemma rt_flags_of_artcells : forall m, artcells m -> rt_flags m.
Proof. intros m A. unfold artcells in A. unfold rt_flags, AMCFLAGS. decompose [and] A. assumption. Qed.
Definition rt_fmin (m : amem) : Prop := rw_cells bsegs m AFMIN [C4 (Z_to_bv 64 8388608)].
Definition rt_bom_sh (m : amem) : Prop :=
  rw_cells bsegs m (shad ABOM) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 5); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249);
                                C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249)].
Definition rt_ctab_sh (m : amem) : Prop := rw_cells bsegs m (shad ACTAB) [CB 32 (repeat (Z_to_bv 8 0) 32)].
(* [comment removed for export] *)
Definition IMG_TABS : list (Z * Z) :=
  [(0x23580, 0x23680); (0x236c0, 0x24498); (0x24800, 0x248b8); (0x248e0, 0x27190); (0x27f40, 0x28040); (0x28080, 0x2a9e0); (0x2aa00, 0x2ac80)].
Definition tab_sh (m : amem) (iv : Z * Z) : Prop :=
  rw_cells bsegs m (shad (fst iv)) [CB (Z.to_nat ((snd iv - fst iv) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((snd iv - fst iv) / 8)))].
Definition img_sh (m : amem) : Prop := Forall (tab_sh m) IMG_TABS.
Lemma img_tabs_bounds : forall lo hi, In (lo, hi) IMG_TABS ->
  0x10000 <= lo /\ lo < hi /\ hi <= 0x671000 /\ lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
  intros lo hi H. unfold IMG_TABS in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; repeat split; first [lia | reflexivity]|]). destruct H.
Qed.
Definition client_x (m : amem) : Prop := rt_real_mc m /\ rt_fmin m /\ rt_bom_sh m /\ rt_ctab_sh m /\ img_sh m.

(* [comment removed for export] *)
Definition client_img (m : amem) : Prop :=
  rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)]
  /\ rw_cells bsegs m AVTAB_IMPL vtab_impl_cells
  /\ rw_cells bsegs m AVTAB_DOM vtab_dom_cells
  /\ client_x m.
Lemma client_img_x : forall m, client_img m -> client_x m.
Proof. intros m (_ & _ & _ & X). exact X. Qed.
(* [comment removed for export] *)
Definition client_x_addr (a : Z) : Prop :=
  (AREAL_MC <= a < AREAL_MC + 16) \/ (AFMIN <= a < AFMIN + 4)
  \/ (shad ABOM <= a < shad ABOM + 8) \/ (shad ACTAB <= a < shad ACTAB + 32)
  \/ (exists lo hi, In (lo, hi) IMG_TABS /\ shad lo <= a < shad lo + (hi - lo) / 8).
(* [comment removed for export] *)
Lemma client_x_addr_num : forall a, client_x_addr a ->
  (AREAL_MC <= a < AREAL_MC + 16) \/ (AFMIN <= a < AFMIN + 4) \/ (shad ABOM <= a < shad ABOM + 8) \/ (shad ACTAB <= a < shad ACTAB + 32)
  \/ (shad 0x23580 <= a < shad 0x23580 + 32) \/ (shad 0x236c0 <= a < shad 0x236c0 + 443) \/ (shad 0x24800 <= a < shad 0x24800 + 23)
  \/ (shad 0x248e0 <= a < shad 0x248e0 + 1302) \/ (shad 0x27f40 <= a < shad 0x27f40 + 32) \/ (shad 0x28080 <= a < shad 0x28080 + 1324)
  \/ (shad 0x2aa00 <= a < shad 0x2aa00 + 80).
Proof.
  intros a [H|[H|[H|[H|(lo & hi & Hin & H)]]]]; [tauto| tauto| tauto| tauto|]. right; right; right; right.
  unfold IMG_TABS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn in H; tauto|]). destruct Hin.
Qed.
Lemma client_x_magree : forall (P : Z -> Prop) mx my, client_x mx -> magree bsegs P mx my -> (forall a, client_x_addr a -> P a) -> client_x my.
Proof.
  intros P mx my (X1 & X2 & X3 & X4 & X5) AG HP. unfold client_x, rt_real_mc, rt_fmin, rt_bom_sh, rt_ctab_sh in *.
  split; [| split; [| split; [| split]]]; [ (eapply rw_cells_magree; [exact AG| eassumption|]); intros a Ha; apply HP; unfold client_x_addr;
    cbn [cells_size csize Nat.add] in Ha; lia .. |].
  unfold img_sh in *. apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) X5 _ Hin) as T.
  unfold tab_sh in T |- *. cbn [fst snd] in T |- *.
  pose proof (img_tabs_bounds lo hi Hin) as (B1 & B2 & B3 & B4 & B5).
  eapply rw_cells_magree; [exact AG| exact T|]. intros a Ha. apply HP. right; right; right; right. exists lo, hi. split; [exact Hin|].
  cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by (apply Z.div_pos; lia). lia.
Qed.

(* [comment removed for export] *)
Definition client_ranges : list (Z * Z) :=
  [(0x10f610, 0x10f640); (0x10f6d0, 0x10f720); (0x64dd80, 0x64dd88); (0x64dda0, 0x64dda2); (0x64de20, 0x64de50); (0x64de80, 0x64de82);
   (* [comment removed for export] *)
   (0x114860, 0x114870); (0x1174c0, 0x1174c4); (0x22f40, 0x22f80); (0x27e00, 0x27f00)] ++ IMG_TABS.

(* [comment removed for export] *)
Definition rt_suar (m : amem) : Prop := rw_cells bsegs m ASUAR [C4 (Z_to_bv 64 1)].

(* [comment removed for export] *)
Definition client_sh_addrs : list Z :=
  [0x10f610; 0x10f618; 0x10f620; 0x10f628; 0x10f630; 0x10f638;
   0x10f6d0; 0x10f6d8; 0x10f6e0; 0x10f6e8; 0x10f6f0; 0x10f6f8; 0x10f700; 0x10f708; 0x10f710; 0x10f718;
   0x64dd80; 0x64dda0; 0x64de20; 0x64de28; 0x64de30; 0x64de38; 0x64de40; 0x64de48; 0x64de80].
Definition client_sh (m : amem) : Prop := forall X, In X client_sh_addrs -> m (wa (shad X)) = Some (Z_to_bv 8 0).
End CANSEC1.
(* [comment removed for export] *)
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xcc200).
(* [comment removed for export] *)
Notation uri_img := client_img (only parsing).
Notation uri_sh := client_sh (only parsing).
Notation uri_img_ranges := client_ranges (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fcell (m : amem) (LB : list ablock) (C k : Z) : Prop :=
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= C /\ C + k <= FA + FN /\ ablk FA (FA + FN) /\ FA + FN + 8 <= KEND /\ FA mod 8 = 0)
  /\ unpoisoned m C (C + k).


Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).

(* [comment removed for export] *)
Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.

(* [comment removed for export] *)
Variable fflag : alayout -> Z -> Z -> Z.      (* [comment removed for export] *)
(* [comment removed for export] *)
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.

Notation FB0 F := (mkABlock (ABFake 0) F 64).

Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

(* [comment removed for export] *)
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Definition SM2_STACK : Z := 4096.
Definition sm2_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (FB2 F :: LB) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 256 /\ rng RNG (shad F) 32
    /\ (forall a, in_block LB a -> m' (wa (shad a)) = m (wa (shad a)))
    /\ (forall a, aclient_addr CI LB (bv_unsigned sp) a -> a < shad F \/ shad F + 32 <= a).   (* [comment removed for export] *)

Definition stack_malloc_2_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 2) F n) LB) ->      (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM2_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm2_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2U) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Notation FB4 F := (mkABlock (ABFake 4) F 1024).
Definition sm4_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (FB4 F :: LB) m'
    /\ F mod 1024 = 0 /\ ablk F (F + 1024) /\ F + 1024 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 992 junk; C8 (Z_to_bv 64 (fflag L 4 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 1024 /\ rng RNG (shad F) 128
    /\ (forall a, in_block LB a -> m' (wa (shad a)) = m (wa (shad a)))   (* [comment removed for export] *)
    /\ (forall a, aclient_addr CI LB (bv_unsigned sp) a -> a < shad F \/ shad F + 128 <= a).   (* [comment removed for export] *)

Definition stack_malloc_4_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 4) F n) LB) ->      (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM4_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm4_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC4) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Notation FB5 F := (mkABlock (ABFake 5) F 2048).
Definition sm5_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (FB5 F :: LB) m'
    /\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 (fflag L 5 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 2048 /\ rng RNG (shad F) 256
    /\ (forall a, in_block LB a -> m' (wa (shad a)) = m (wa (shad a)))   (* [comment removed for export] *)
    /\ (forall a, aclient_addr CI LB (bv_unsigned sp) a -> a < shad F \/ shad F + 256 <= a).   (* [comment removed for export] *)

Definition stack_malloc_5_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 5) F n) LB) ->      (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM5_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm5_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC5) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition stack_malloc_4_stmt1 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall F1 n1 F2 n2, In (mkABlock (ABFake 4) F1 n1) LB -> In (mkABlock (ABFake 4) F2 n2) LB -> F1 = F2) ->   (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM4_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm4_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC4) fc None m (seg_rom bsegs)).
Definition stack_malloc_5_stmt1 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB -> In (mkABlock (ABFake 5) F2 n2) LB -> F1 = F2) ->   (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM5_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm5_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC5) fc None m (seg_rom bsegs)).
Lemma sm4_of_sm4_1 : stack_malloc_4_stmt1 -> stack_malloc_4_stmt.
Proof.
  intros H. unfold stack_malloc_4_stmt. intros until lo. intros AH NOF. apply H; [exact AH|].
  intros F1 n1 F2 n2 H1 _. exfalso. exact (NOF F1 n1 H1).
Qed.
Lemma sm5_of_sm5_1 : stack_malloc_5_stmt1 -> stack_malloc_5_stmt.
Proof.
  intros H. unfold stack_malloc_5_stmt. intros until lo. intros AH NOF. apply H; [exact AH|].
  intros F1 n1 F2 n2 H1 _. exfalso. exact (NOF F1 n1 H1).
Qed.

(* [comment removed for export] *)
Definition SF5_STACK : Z := 16.
Definition sf5_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st LB m'
    /\ (forall a, in_block LB a -> m' (wa (shad a)) = m (wa (shad a))).   (* [comment removed for export] *)

Definition stack_free_5_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo F : Z),
  AHEAP AI L RNG st (FB5 F :: LB) m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SF5_STACK ->
  a0 = Z_to_bv 64 F ->
  rw_cells bsegs m (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (sf5_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKFREE5) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition amemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at bsegs m' (bv_unsigned a1) src.

Definition asan_memcpy_stmt : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
  let D := bv_unsigned a0 in let S := bv_unsigned a1 in let n := bv_unsigned a2 in
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AMEMCPY_STACK -> KHIGH <= lo ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  bytes_at bsegs m S src -> length src = Z.to_nat n ->
  rw_cells bsegs m D [CB (Z.to_nat n) junk] ->
  (S + n <= D \/ D + n <= S) ->
  (S + n <= bv_unsigned sp - AMEMCPY_STACK \/ bv_unsigned sp <= S) ->
  (D + n <= lo \/ bv_unsigned sp <= D) ->
  app_blk S (S + n) -> app_blk D (D + n) ->
  unpoisoned m S (S + n) -> unpoisoned m D (D + n) ->
  n <= 2^40 ->
  (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
  (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
  wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S n -> rng RNG D n ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF bsegs RNG (amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc a0 a1 a2 src lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AMEMCPY) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC2.
