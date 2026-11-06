From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcDecl.
Import ListNotations.
Open Scope Z_scope.

(* declaration_of in the asan-ubsan image (patched entry 0x83114): a 32-byte frame (ra, s0, s1 in [sp - 24, sp)), a
   shadow check before each of its own loads of the row and stores to o (s1 holds the shadow offset, read through the
   GOT slot 0xa08f0), the slot table filled by its own byte loops, the two copies through __asan_memcpy (0x52164), and
   the UBSan checks (m mod 8, no wrap of o + j) that trap at the `unimp` at 0x83534. *)
Definition DECLARATION_OF : Z := 0x83114.
Definition DECLARATION_OF_FRAME : Z := 32.
(* K = 32 + K(__asan_memcpy) 2224 (contracts/libreac/declaration_of@fuzz_ctrl.md Names). *)
Definition DECLARATION_OF_K : Z := 2256.
Definition BOX_CATALOGUE : Z := 0x9f620.

(* The ubsan post (lib/U/Prog/declaration_of_c.v) with the window K of this build, and the runtime's cells and the
   shadow kept. *)
Definition declaration_of_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if decl_ok row then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - DECLARATION_OF_K, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 32)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' (bv_unsigned a1) [CB 32 (if decl_ok row then decl row else ob)] /\
    bytes_at rsegs m' (bv_unsigned a0) row /\
    asan_cells m' /\ shadow_rw m'.

(* The ubsan contract (lib/U/Prog/declaration_of_c.v) with the window K, and the premises of the asan-ubsan build
   (S1.4 and S1.5 of the English contract and those of __asan_memcpy at the copies to o and o + 20): the runtime's
   cells and shadow, the 296 bytes at m and the 32 bytes at o addressable, the end of o in AppMem, the window in AppMem
   above the shadow, and the 32 bytes at o apart from [RT_LO, RT_HI). The UBSan checks pass from m mod 8 = 0 and
   o + 32 <= APPMEM_END (addressable). *)
Definition declaration_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DECLARATION_OF_K <= bv_unsigned sp ->
    bv_unsigned a0 mod 8 = 0 ->
    length row = 296%nat ->
    bytes_at rsegs m (bv_unsigned a0) row ->
    rw_cells rsegs m (bv_unsigned a1) [CB 32 ob] ->
    bv_unsigned a1 + 32 <= bv_unsigned a0 \/ bv_unsigned a0 + 296 <= bv_unsigned a1 ->
    bv_unsigned a0 + 296 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a0 ->
    bv_unsigned a1 + 32 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a1 ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 296 -> addressable m (bv_unsigned a1) 32 ->
    app_mem (bv_unsigned a1 + 32) ->
    (bv_unsigned a1 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a1) ->
    evt rsegs (declaration_of_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DECLARATION_OF) fc None m (seg_rom rsegs)).

Definition declaration_of_rows : Prop :=
  forall i, (i < 11)%nat -> exists row,
    image_bytes rsegs (BOX_CATALOGUE + 296 * Z.of_nat i) 296 = Some row /\
    decl_ok row = true /\ map bv_unsigned (decl row) = nth i decl_table [].

(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint RNG, with one rng
   premise per region the run reads or writes (data accesses only: an instruction fetch is not an access of evtF).
   The regions: the image [IMG_LO, IMG_HI) (lib/B/Prog/ImgBounds.v), which the footprint contract of __asan_memcpy
   (lib/B/Prog/asan_memcpy_cF.v) takes for its code, GOT cells and runtime cells; the window K below sp (the frame
   stores and loads of this image's own code, and the window of __asan_memcpy below it); the 8-ALIGNED shadow word
   span of that window (sh_word_rng of rng_asan.v), which holds the shadow of __asan_memcpy's frame that its
   contract takes; the runtime words [RT_LO, RT_HI), which hold both the GOT slot 0xa08f0 and the cell of the shadow
   offset; the 296 bytes of the row at a0, read by this code and by the source side of the two copies; the 32 bytes
   at a1, stored by this code and written by the destination side of the two copies; and the shadow bytes of those
   two ranges. Each shadow premise is the 8-ALIGNED shadow word cover of its range, because __asan_memcpy's quick
   check loads whole aligned shadow words; the byte-exact spans that this image's own 1-byte shadow loads need lie
   inside it. No range is named for the image data of the slot table at BOX_CATALOGUE: this run never loads it
   (declaration_of_rows is a statement about the image, not about the run). The rng_bytes premise
   (lib/Lib/RngBytes.v) says the footprint is decided byte by byte; the footprint contract of __asan_memcpy, which
   this run calls, takes it.
   declaration_of_contract_of_F gives the old statement back with RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memcpy_cF.

Definition declaration_of_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DECLARATION_OF_K <= bv_unsigned sp ->
    bv_unsigned a0 mod 8 = 0 ->
    length row = 296%nat ->
    bytes_at rsegs m (bv_unsigned a0) row ->
    rw_cells rsegs m (bv_unsigned a1) [CB 32 ob] ->
    bv_unsigned a1 + 32 <= bv_unsigned a0 \/ bv_unsigned a0 + 296 <= bv_unsigned a1 ->
    bv_unsigned a0 + 296 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a0 ->
    bv_unsigned a1 + 32 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a1 ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 296 -> addressable m (bv_unsigned a1) 32 ->
    app_mem (bv_unsigned a1 + 32) ->
    (bv_unsigned a1 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a1) ->
    (* the footprint *)
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K ->
    sh_word_rng RNG (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG (bv_unsigned a0) 296 ->
    rng RNG ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
            (((bv_unsigned a0 + 295) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8) ->
    rng RNG (bv_unsigned a1) 32 ->
    rng RNG ((bv_unsigned a1 / 8 + ASAN_K) / 8 * 8)
            (((bv_unsigned a1 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a1 / 8 + ASAN_K) / 8 * 8) ->
    evtF rsegs RNG (declaration_of_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DECLARATION_OF) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access (every rng premise by rng_all). *)
Lemma declaration_of_contract_of_F : declaration_of_contract_F -> declaration_of_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE HSW HHM HAE HADm HADo HAPo HRTo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HADm as (ADm0 & _ & ADm2 & _). pose proof HADo as (ADo0 & _ & ADo2 & _).
  assert (RBY : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (RIMG : rng RNG_all IMG_LO (IMG_HI - IMG_LO))
    by (pose proof two64 as H64; apply rng_all; cbv [IMG_LO IMG_HI]; lia).
  assert (RWIN : rng RNG_all (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K)
    by (apply rng_all; unfold DECLARATION_OF_K, HIGHMEM_BEG in *; lia).
  assert (RWS : sh_word_rng RNG_all (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K)
    by (apply sh_word_rng_all; unfold DECLARATION_OF_K, HIGHMEM_BEG in *; lia).
  assert (RRT : rng RNG_all RT_LO (RT_HI - RT_LO)) by (apply rng_all; unfold RT_LO, RT_HI; lia).
  assert (RROW : rng RNG_all (bv_unsigned a0) 296) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSm : rng RNG_all ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a0 + 295) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8))
    by (apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia).
  assert (ROUT : rng RNG_all (bv_unsigned a1) 32) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSo : rng RNG_all ((bv_unsigned a1 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a1 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a1 / 8 + ASAN_K) / 8 * 8))
    by (apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia).
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE HSW HHM HAE HADm HADo HAPo HRTo
               RBY RIMG RWIN RWS RRT RROW RSm ROUT RSo)).
Qed.

(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; wave lead a Theorem Labs lane, form of ASSIGN.md (a working note, not in this delivery) and its 10:34Z amendment): the
   _on twins of the statements above. The run needs shadow bytes present through the universal `shadow_rw m`
   premise only at its calls (declaration_of.v): the two copies through __asan_memcpy and the fills through
   __asan_memset, whose _on contracts (asan_memcpy_c_on.v, asan_memset_c_on.v) take the aligned 8-byte shadow words
   (sh_word_on.v) of their source and destination ranges. It stores no shadow byte. Its own checks of the row at a0 and
   of the 32 bytes at a1 read their shadow through `addressable` (rt_shadow_rd and rt_addressable of RcAsanRT.v), not
   through shadow_rw. The calls and their ranges (o = a1, row = a0, |P| the bytes of o written before the call):
     __asan_memcpy(o, a0 + 24, 32)                  source sh_word_on (a0 + 24) 32, destination sh_word_on o 32
     __asan_memcpy(o + 20, a0 + 254, 11)            source sh_word_on (a0 + 254) 11, destination inside o's 32 bytes
     __asan_memset(o + |P|, v, n), |P| + n <= 32   destination inside o's 32 bytes
   so declaration_of_shadow_R a0 a1 is the union: the two source spans and the span of o. The post's `shadow_rw m'`
   becomes: each shadow region the caller holds in m it holds in m'. No other premise or conjunct changes. The old
   statements follow from the twins: declaration_of_contract_of_on, declaration_of_contract_F_of_F_on;
   declaration_of_contract_on_of_F_on is declaration_of_contract_of_F for the twins. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require sh_word_on.

Definition declaration_of_shadow_R (a0 a1 : Z) (a : Z) : Prop :=
  B.Prog.sh_word_on.sh_word_on (a0 + 24) 32 a \/ B.Prog.sh_word_on.sh_word_on (a0 + 254) 11 a \/
  B.Prog.sh_word_on.sh_word_on a1 32 a.

Definition declaration_of_post_on (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if decl_ok row then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - DECLARATION_OF_K, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 32)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' (bv_unsigned a1) [CB 32 (if decl_ok row then decl row else ob)] /\
    bytes_at rsegs m' (bv_unsigned a0) row /\
    asan_cells m' /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').

Definition declaration_of_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DECLARATION_OF_K <= bv_unsigned sp ->
    bv_unsigned a0 mod 8 = 0 ->
    length row = 296%nat ->
    bytes_at rsegs m (bv_unsigned a0) row ->
    rw_cells rsegs m (bv_unsigned a1) [CB 32 ob] ->
    bv_unsigned a1 + 32 <= bv_unsigned a0 \/ bv_unsigned a0 + 296 <= bv_unsigned a1 ->
    bv_unsigned a0 + 296 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a0 ->
    bv_unsigned a1 + 32 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a1 ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> B.ShadowRwOn.shadow_rw_on (declaration_of_shadow_R (bv_unsigned a0) (bv_unsigned a1)) m ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 296 -> addressable m (bv_unsigned a1) 32 ->
    app_mem (bv_unsigned a1 + 32) ->
    (bv_unsigned a1 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a1) ->
    evt rsegs (declaration_of_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DECLARATION_OF) fc None m (seg_rom rsegs)).

Definition declaration_of_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DECLARATION_OF_K <= bv_unsigned sp ->
    bv_unsigned a0 mod 8 = 0 ->
    length row = 296%nat ->
    bytes_at rsegs m (bv_unsigned a0) row ->
    rw_cells rsegs m (bv_unsigned a1) [CB 32 ob] ->
    bv_unsigned a1 + 32 <= bv_unsigned a0 \/ bv_unsigned a0 + 296 <= bv_unsigned a1 ->
    bv_unsigned a0 + 296 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a0 ->
    bv_unsigned a1 + 32 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= bv_unsigned a1 ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> B.ShadowRwOn.shadow_rw_on (declaration_of_shadow_R (bv_unsigned a0) (bv_unsigned a1)) m ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 296 -> addressable m (bv_unsigned a1) 32 ->
    app_mem (bv_unsigned a1 + 32) ->
    (bv_unsigned a1 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a1) ->
    (* the footprint *)
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K ->
    sh_word_rng RNG (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG (bv_unsigned a0) 296 ->
    rng RNG ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
            (((bv_unsigned a0 + 295) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8) ->
    rng RNG (bv_unsigned a1) 32 ->
    rng RNG ((bv_unsigned a1 / 8 + ASAN_K) / 8 * 8)
            (((bv_unsigned a1 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a1 / 8 + ASAN_K) / 8 * 8) ->
    evtF rsegs RNG (declaration_of_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DECLARATION_OF) fc None m (seg_rom rsegs)).

(* The old post from the twin's: under the universal premise, the region transport at the whole shadow
   (P := fun _ => True, shadow_rw_on_of_shadow_rw and shadow_rw_of_on_all) gives `shadow_rw m'` back. *)
Lemma declaration_of_post_of_on : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob ms',
  shadow_rw m ->
  declaration_of_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob ms' ->
  declaration_of_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob ms'.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob ms' HSW
    (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
     & E & MU & WM & MI & ST & HO & HR & AC & SR).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  refine (conj E (conj MU (conj WM (conj MI (conj ST (conj HO (conj HR (conj AC _)))))))).
  apply B.ShadowRwOn.shadow_rw_of_on_all, SR, B.ShadowRwOn.shadow_rw_on_of_shadow_rw, HSW.
Qed.

(* The old statement from the twin: the universal premise gives the region (shadow_rw_on_of_shadow_rw), and
   declaration_of_post_of_on gives the old post. *)
Lemma declaration_of_contract_of_on : declaration_of_contract_on -> declaration_of_contract.
Proof.
  intros HON ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE HSW HHM HAE HADm HADo HAPo HRTo.
  eapply evt_mono.
  - exact (HON ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE
             (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE HADm HADo HAPo HRTo).
  - intros ms' H. exact (declaration_of_post_of_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HSW H).
Qed.

(* The same for the footprint statements. *)
Lemma declaration_of_contract_F_of_F_on : declaration_of_contract_F_on -> declaration_of_contract_F.
Proof.
  intros HON RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE HSW HHM HAE HADm HADo HAPo HRTo
    RBY RIMG RWIN RWS RRT RROW RSm ROUT RSo.
  eapply evtF_mono.
  - exact (HON RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE
             (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE HADm HADo HAPo HRTo
             RBY RIMG RWIN RWS RRT RROW RSm ROUT RSo).
  - intros ms' H. exact (declaration_of_post_of_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HSW H).
Qed.

(* declaration_of_contract_of_F for the twins: the _F twin at RNG_all gives the plain twin. *)
Lemma declaration_of_contract_on_of_F_on : declaration_of_contract_F_on -> declaration_of_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE HSW HHM HAE HADm HADo HAPo HRTo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HADm as (ADm0 & _ & ADm2 & _). pose proof HADo as (ADo0 & _ & ADo2 & _).
  assert (RBY : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (RIMG : rng RNG_all IMG_LO (IMG_HI - IMG_LO))
    by (pose proof two64 as H64; apply rng_all; cbv [IMG_LO IMG_HI]; lia).
  assert (RWIN : rng RNG_all (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K)
    by (apply rng_all; unfold DECLARATION_OF_K, HIGHMEM_BEG in *; lia).
  assert (RWS : sh_word_rng RNG_all (bv_unsigned sp - DECLARATION_OF_K) DECLARATION_OF_K)
    by (apply sh_word_rng_all; unfold DECLARATION_OF_K, HIGHMEM_BEG in *; lia).
  assert (RRT : rng RNG_all RT_LO (RT_HI - RT_LO)) by (apply rng_all; unfold RT_LO, RT_HI; lia).
  assert (RROW : rng RNG_all (bv_unsigned a0) 296) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSm : rng RNG_all ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a0 + 295) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8))
    by (apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia).
  assert (ROUT : rng RNG_all (bv_unsigned a1) 32) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSo : rng RNG_all ((bv_unsigned a1 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a1 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a1 / 8 + ASAN_K) / 8 * 8))
    by (apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia).
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo row ob ST HLO HM8 HLEN HROW HO DMO DMS DOS MI HCE HSW HHM HAE HADm HADo HAPo HRTo
               RBY RIMG RWIN RWS RRT RROW RSm ROUT RSo)).
Qed.

