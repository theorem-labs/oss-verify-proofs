From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
Import ListNotations.
Open Scope Z_scope.

(* reac_identity_init in the asan-ubsan image: `addi sp,sp,-16`, `sd ra,8(sp)`, `beqz a0`, then `li a2,38`,
   `li a1,0` and `jal __asan_memset` (0x52600), then `ld ra,8(sp)`, `addi sp,sp,16`, `ret`. The code has no shadow
   check and no UBSan check of its own: its only memory accesses are the store and the load of ra in its 16-byte
   frame. *)
Definition REAC_IDENTITY_INIT : Z := 0x87de8.
Definition REAC_IDENTITY_INIT_FRAME : Z := 16.
(* The stack bound: the 16-byte frame plus __asan_memset's ASAN_MEMSET_K = 2208 bytes below it. *)
Definition REAC_IDENTITY_INIT_K : Z := 2224.

Definition reac_identity_init_W (sp id : Z) : list ivl :=
  [(sp - REAC_IDENTITY_INIT_K, sp); (id, id + 38)].

Definition reac_identity_init_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (lo id : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (reac_identity_init_W (bv_unsigned sp) id) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m' /\ shadow_rw m'
    /\ (id = 0 -> munch [(bv_unsigned sp - REAC_IDENTITY_INIT_FRAME, bv_unsigned sp)] m m')
    /\ (id <> 0 -> rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)]).

Definition reac_identity_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id : Z) (idb : list byte),
    a0 = Z_to_bv 64 id -> 0 <= id < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INIT_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38 /\ end_in_app id 38) ->
    (id <> 0 -> id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INIT_K \/ bv_unsigned sp <= id) ->
    evt rsegs (reac_identity_init_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INIT) fc None m (seg_rom rsegs)).

(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint RNG. The function's
   own accesses are the save and load of ra in its 16-byte frame; the rest of the window [sp - K, sp) and the 38
   bytes at id (with their shadow bytes and the runtime's cells) are touched by its one callee, __asan_memset, so the
   premises cover the image [IMG_LO, IMG_HI) (lib/B/Prog/ImgBounds.v), which the footprint contract of
   __asan_memset (lib/B/Prog/asan_memset_cF.v) takes for its code, GOT cells and runtime cells; the whole window;
   the 8-ALIGNED shadow word span of the window (sh_word_rng of rng_asan.v), which holds the shadow of the
   frame of __asan_memset that its contract takes; the runtime words [RT_LO, RT_HI); and the data range with its
   shadow bytes. The shadow premise of the data range is the 8-ALIGNED shadow word cover [shadow_addr id / 8 * 8,
   shadow_addr (id + 37) / 8 * 8 + 8): __asan_memset's quick check loads whole aligned shadow words. The rng_bytes
   premise (lib/Lib/RngBytes.v) says the footprint is decided byte by byte; the footprint contract of
   __asan_memset takes it.
   reac_identity_init_contract_of_F gives the old statement back with RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memset_cF.

Definition reac_identity_init_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id : Z) (idb : list byte),
    a0 = Z_to_bv 64 id -> 0 <= id < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INIT_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38 /\ end_in_app id 38) ->
    (id <> 0 -> id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INIT_K \/ bv_unsigned sp <= id) ->
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    rng RNG ((bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
            ((bv_unsigned sp - 1) / 8 - (bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + 1) ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    (id <> 0 -> rng RNG id 38 /\
                rng RNG ((id / 8 + ASAN_K) / 8 * 8)
                        (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)) ->
    evtF rsegs RNG (reac_identity_init_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INIT) fc None m (seg_rom rsegs)).

From Stdlib Require Import Lia.

(* The old statement is the _F statement at the footprint that admits every access (every rng premise by rng_all). *)
Lemma reac_identity_init_contract_of_F : reac_identity_init_contract_F -> reac_identity_init_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  assert (RBY : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (RIMG : rng RNG_all IMG_LO (IMG_HI - IMG_LO))
    by (pose proof two64 as H64; apply rng_all; cbv [IMG_LO IMG_HI]; lia).
  assert (RW : rng RNG_all (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K)
    by (clear - Rsp HLO HHM; apply rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG in *; lia).
  assert (RWSA : sh_word_rng RNG_all (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K)
    by (clear - Rsp HLO HHM HAE; apply sh_word_rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG in *; lia).
  assert (RWS : rng RNG_all ((bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
                  ((bv_unsigned sp - 1) / 8 - (bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + 1))
    by (clear - Rsp HLO HHM HAE; apply rng_all;
        unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia).
  assert (RRT : rng RNG_all RT_LO (RT_HI - RT_LO)) by (apply rng_all; unfold RT_LO, RT_HI; lia).
  assert (RID : id <> 0 -> rng RNG_all id 38 /\
                rng RNG_all ((id / 8 + ASAN_K) / 8 * 8)
                            (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)).
  { intros E. destruct (HAD E) as ((H0 & _ & H1 & _) & _). clear - H0 H1.
    split; apply rng_all; unfold APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia. }
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP RBY RIMG RW RWSA RWS RRT RID)).
Qed.

(* ---- Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; wave lead a Theorem Labs lane, form of ASSIGN.md (a working note, not in this delivery)): the _on forms.  The function has
   no shadow check and no shadow store of its own (header above); the only shadow bytes its run needs present are its
   one callee's: __asan_memset(id, 0, 38), called only when id <> 0, whose region is asan_memset_shadow_R a0 a2 :=
   sh_word_on (bv_unsigned a0) (bv_unsigned a2) (a Theorem Labs lane's asan_memset_c_on.v) at a0 = id, a2 = 38.  So R =
   (id <> 0 /\ sh_word_on id 38), stated with that same predicate.  The post's `shadow_rw m'` becomes the wave's
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`.  The old statements follow (reac_identity_init_contract_of_on,
   _F_of_F_on).  Writer: a Theorem Labs lane. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require sh_word_on.

Definition reac_identity_init_shadow_R (id a : Z) : Prop := id <> 0 /\ B.Prog.sh_word_on.sh_word_on id 38 a.

Definition reac_identity_init_post_on (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (lo id : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (reac_identity_init_W (bv_unsigned sp) id) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m'
    /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m')
    /\ (id = 0 -> munch [(bv_unsigned sp - REAC_IDENTITY_INIT_FRAME, bv_unsigned sp)] m m')
    /\ (id <> 0 -> rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)]).

Definition reac_identity_init_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id : Z) (idb : list byte),
    a0 = Z_to_bv 64 id -> 0 <= id < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INIT_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> B.ShadowRwOn.shadow_rw_on (reac_identity_init_shadow_R id) m ->
    (id <> 0 -> addressable m id 38 /\ end_in_app id 38) ->
    (id <> 0 -> id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INIT_K \/ bv_unsigned sp <= id) ->
    evt rsegs (reac_identity_init_post_on ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INIT) fc None m (seg_rom rsegs)).

Definition reac_identity_init_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id : Z) (idb : list byte),
    a0 = Z_to_bv 64 id -> 0 <= id < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INIT_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> B.ShadowRwOn.shadow_rw_on (reac_identity_init_shadow_R id) m ->
    (id <> 0 -> addressable m id 38 /\ end_in_app id 38) ->
    (id <> 0 -> id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INIT_K \/ bv_unsigned sp <= id) ->
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    rng RNG ((bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
            ((bv_unsigned sp - 1) / 8 - (bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + 1) ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    (id <> 0 -> rng RNG id 38 /\
                rng RNG ((id / 8 + ASAN_K) / 8 * 8)
                        (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)) ->
    evtF rsegs RNG (reac_identity_init_post_on ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INIT) fc None m (seg_rom rsegs)).

(* With the universal premise the _on post gives the old post back (P := fun _ => True). *)
Lemma reac_identity_init_post_of_on : forall ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id,
  shadow_rw m -> forall ms',
  reac_identity_init_post_on ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id ms' ->
  reac_identity_init_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id ms'.
Proof.
  intros ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id HSW ms'
    (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
     E & MU & WM & MI & ST & AC & SW & H0 & H1).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  refine (conj E (conj MU (conj WM (conj MI (conj ST (conj AC (conj _ (conj H0 H1)))))))).
  exact (B.ShadowRwOn.shadow_rw_of_on_all m' (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ _ HSW))).
Qed.

Lemma reac_identity_init_contract_of_on : reac_identity_init_contract_on -> reac_identity_init_contract.
Proof.
  intros HON ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP.
  eapply evt_mono.
  - exact (HON ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ _ HSW)
             HAD HRT HSP).
  - exact (reac_identity_init_post_of_on ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id HSW).
Qed.

Lemma reac_identity_init_contract_F_of_F_on : reac_identity_init_contract_F_on -> reac_identity_init_contract_F.
Proof.
  intros HON RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP RBY RIMG RW RWSA RWS RRT RID.
  eapply evtF_mono.
  - exact (HON RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ _ HSW)
             HAD HRT HSP RBY RIMG RW RWSA RWS RRT RID).
  - exact (reac_identity_init_post_of_on ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id HSW).
Qed.

(* The _on statement is the _F_on statement at the footprint that admits every access (as contract_of_F). *)
Lemma reac_identity_init_contract_on_of_F_on : reac_identity_init_contract_F_on -> reac_identity_init_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  assert (RBY : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (RIMG : rng RNG_all IMG_LO (IMG_HI - IMG_LO))
    by (pose proof two64 as H64; apply rng_all; cbv [IMG_LO IMG_HI]; lia).
  assert (RW : rng RNG_all (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K)
    by (clear - Rsp HLO HHM; apply rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG in *; lia).
  assert (RWSA : sh_word_rng RNG_all (bv_unsigned sp - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K)
    by (clear - Rsp HLO HHM HAE; apply sh_word_rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG in *; lia).
  assert (RWS : rng RNG_all ((bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
                  ((bv_unsigned sp - 1) / 8 - (bv_unsigned sp - REAC_IDENTITY_INIT_K) / 8 + 1))
    by (clear - Rsp HLO HHM HAE; apply rng_all;
        unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia).
  assert (RRT : rng RNG_all RT_LO (RT_HI - RT_LO)) by (apply rng_all; unfold RT_LO, RT_HI; lia).
  assert (RID : id <> 0 -> rng RNG_all id 38 /\
                rng RNG_all ((id / 8 + ASAN_K) / 8 * 8)
                            (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)).
  { intros E. destruct (HAD E) as ((H0 & _ & H1 & _) & _). clear - H0 H1.
    split; apply rng_all; unfold APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia. }
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo id idb Ha0 Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP
               RBY RIMG RW RWSA RWS RRT RID)).
Qed.

