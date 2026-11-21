(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit AF_atexit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.

(* [comment removed for export] *)
End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

Section CANSEC2. Context {rc : runConstT}.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_rt (m : mem) : Prop :=
     rw_cells bsegs m 0xd1380 [C8 (Z_to_bv 64 0x169620)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd1390 [C8 (Z_to_bv 64 0x16b6a8); C8 (Z_to_bv 64 0xd7378); C8 (Z_to_bv 64 0xd9b78);
                                C8 (Z_to_bv 64 0xda868); C8 (Z_to_bv 64 0xda870); C8 (Z_to_bv 64 0xda860)]  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd13c0 [C8 (Z_to_bv 64 0xd3258)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd3250 [C8 (Z_to_bv 64 0xc76dc); C8 (Z_to_bv 64 0xc7ae0)]              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd9b78 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xda858 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd93dc [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 18446744073709551615)]                                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd7390 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0xd1380 \/ (0xd13c8 <= lo /\ hi <= 0xd3250) \/ (0xd3260 <= lo /\ hi <= 0xd7390) \/ (0xd7394 <= lo /\ hi <= 0xd93dc)
   \/ (0xd93dd <= lo /\ hi <= 0xd9b78) \/ (0xd9b80 <= lo /\ hi <= 0xda858) \/ (0xda85a <= lo /\ hi <= 0x16b720) \/ 0x16b728 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0xd1380 <= A /\ A + n <= 0xd13c8) \/ (0xd3250 <= A /\ A + n <= 0xd3260) \/ (0xd7390 <= A /\ A + n <= 0xd7394)
              \/ (0xd93dc <= A /\ A + n <= 0xd93dd) \/ (0xd9b78 <= A /\ A + n <= 0xd9b80) \/ (0xda858 <= A /\ A + n <= 0xda85a)
              \/ (0x16b720 <= A /\ A + n <= 0x16b728)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sb sl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma poison_low_spec : forall RNG (sb sl : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  mdtor_rt m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x67f000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF bsegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fa38) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  carve_frame 64%nat ST.
  do 8 hstep.                                          (* [comment removed for export] *)
  hstep. if_true.                                      (* [comment removed for export] *)
  zstep. hstep. if_cases K1; zify_cond K1.              (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 hstep.                                          (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K8; zify_cond K8.
  { exfalso. apply K8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  do 2 zstep.                                          (* [comment removed for export] *)
  hstep. if_cases K9; zify_cond K9. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases K10; zify_cond K10; [exfalso; lia|]. (* [comment removed for export] *)
  do 5 zstep.                                          (* [comment removed for export] *)
  assert (E1 : Z.land (Z.shiftr (addr + size + -8) 3 + 1) 18446744073709551615 - Z.shiftr addr 3 = shn size).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr addr 3) with (shd addr).
  hstep. if_false.                                     (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases KT; zify_cond KT.                    (* [comment removed for export] *)
  2:{ exfalso. lia. }
  do 3 hstep. do 8 hstep.                              (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold poison_low_post. destruct_exs PO.
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  do 16 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros xq Hxq. cbn in Hxq |- *. tauto. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  split. 2: exact DST2.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
  eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end. exact FR'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_one_post (spv d sb sl se : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x4b2e4) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x16b6a8) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1c2b4) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xd3258) s8 (Z_to_bv 64 0xd7378)
                  (Z_to_bv 64 0xd9b78) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x4b2e4) fc None m' (seg_rom bsegs)
    /\ munch [(sb, se)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma unreg_one_spec : forall RNG (sb sl se : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv bsegs m -> mdtor_rt m ->
  rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 (swr mod 256))] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 524288 -> 0x10000 <= beg -> beg + swr <= 0x67f000 ->
  0x10000 <= d -> d + 64 <= 0x67f000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr -> se = sb + sl ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF bsegs RNG (unreg_one_post spv d sb sl se gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x16b6a8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1c2b4) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xd3258) s8 (Z_to_bv 64 0xd7378)
             (Z_to_bv 64 0xd9b78) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b2fc) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 65536).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  do 7 hstep.
  hstep. if_false.                                     (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. if_true.                                      (* [comment removed for export] *)
  hstep. if_false.                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 2 hstep. do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K3; zify_cond K3.
  { exfalso. apply K3. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  hstep. zstep. rewrite (unsigned_lit8 (swr mod 256)) by (apply Z.mod_pos_bound; lia). hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear -SL. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  do 6 hstep. hstep. if_false.
  (* [comment removed for export] *)
  do 3 hstep. do 5 zstep. hstep. do 3 zstep.
  assert (E1 : Z.land (2147450880 + Z.shiftr (beg + swr + -8) 3 + 1) 18446744073709551615 - Z.land (2147450880 + Z.shiftr beg 3) 18446744073709551615
               = shn swr).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite !Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr beg 3) with (shd beg).
  hstep. if_cases KT; zify_cond KT. 2:{ exfalso. lia. }  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold unreg_one_post. destruct_exs PO.
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  cbn [ret_pc reg_get].
  replace (ret_pc (Z_to_bv 64 0x4b2e4)) with (Z_to_bv 64 0x4b2e4 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
     rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 (swr mod 256))].

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells bsegs m 0xd2018 [C8 (Z_to_bv 64 0xd5cc0); C8 (Z_to_bv 64 0xd64c0)]     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd64c0 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd7430 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ gdesc m 0xd5cc0 0x22760 0x4 0x20 0x1d202 0x22780 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5d00 0x22840 0x26 0x60 0x19aaa 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5d40 0x228a0 0x17 0x40 0x1fcd3 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5d80 0x228e0 0x1b 0x40 0x21dd6 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5dc0 0x22920 0x14 0x40 0x14bfa 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5e00 0x22960 0x19 0x40 0x13a96 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5e40 0x229a0 0x14 0x40 0x1e2e8 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5e80 0x229e0 0x13 0x40 0x1937f 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5ec0 0x22a20 0x1d 0x40 0x1b426 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5f00 0x22a60 0x24 0x60 0x114ed 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5f40 0x22ac0 0x19 0x40 0x16df9 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5f80 0x22b00 0x1a 0x40 0x20fd8 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd5fc0 0x22b40 0x25 0x60 0x114f4 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6000 0x22ba0 0x1c 0x40 0x1ad36 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6040 0x22be0 0x16 0x40 0x20fe0 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6080 0x22c20 0x1c 0x40 0x1f1f8 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd60c0 0x22c60 0x16 0x40 0x1d207 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6100 0x22ca0 0x1e 0x40 0x1a532 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6140 0x22ce0 0x15 0x40 0x1c946 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6180 0x22d20 0x17 0x40 0x11d18 0x22d60 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd61c0 0x22da0 0x400 0x500 0x15ef5 0x246a0 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6200 0x232a0 0x1000 0x1400 0x19386 0x246a0 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6240 0x246e0 0x3e 0x60 0x11d20 0x25300 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6280 0x24740 0x3e 0x60 0x1dc16 0x25300 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd62c0 0x247a0 0x40 0x60 0x176c3 0x25300 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6300 0x24800 0x40 0x60 0x15eff 0x25300 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6340 0x24860 0x800 0xa00 0x15482 0x25300 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6380 0x25260 0x80 0xa0 0x11d34 0x25300 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd63c0 0x25340 0x1e 0x40 0x1d202 0x25400 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6400 0x25380 0x16 0x40 0x1fcd3 0x25400 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6440 0x253c0 0x1c 0x40 0x21dd6 0x25400 (2^64 - 1)     (* [comment removed for export] *)
  /\ gdesc m 0xd6480 0x60c200 0x40000 0x50000 0x1c93f 0x22703 (2^64 - 1)     (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc4ec [CB 4 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc508 [CB 12 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc514 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc51c [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc524 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc52c [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc534 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc53c [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc544 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc54c [CB 12 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc558 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc560 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc568 [CB 12 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc574 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc57c [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc584 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc58c [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc594 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc59c [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc5a4 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc5b4 [CB 160 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc654 [CB 640 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc8dc [CB 12 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc8e8 [CB 12 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc8f4 [CB 12 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc900 [CB 12 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc90c [CB 320 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffca4c [CB 20 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffca68 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffca70 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffca78 [CB 8 j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x800b9840 [CB (Z.to_nat 40960) j])                                  (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x80012b98 [CB 256 j]).                                (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac tr_one MU WM D H :=
  lazymatch type of H with
  | _ /\ _ => let Ha := fresh "Ha" in let Hb := fresh "Hb" in destruct H as [Ha Hb]; split; [tr_one MU WM D Ha | tr_one MU WM D Hb]
  | exists _, _ => let j := fresh "j" in let Hj := fresh "Hj" in destruct H as [j Hj]; exists j; tr_one MU WM D Hj
  | _ => eapply rw_cells_transport; [exact H | exact MU | exact WM | apply D; cbn; lia]
  end.

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800c3e08 -> 0x67cfac <= A \/ (0xd6511 <= A /\ A + n <= 0x67cd88) \/ A + n <= 0xd6510 ->
              disjoint_from (AEXIT_W1 sp) A n).
  { intros A n Hn HA HO. unfold AEXIT_W1, MDTOR_DEPTH. cbn. lia. }
  unfold mdtor_pre, gdesc in *.
  destruct P as (RT & P).
  assert (RT' : mdtor_rt m').
  { eapply mdtor_rt_frame; [exact RT | exact MU | exact WM | ]. unfold AEXIT_W1, MDTOR_DEPTH.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  refine (conj RT' _). clear RT RT'.
  tr_one MU WM D P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC2.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Ltac hstep ::= zstep; fix_lit_store.
Ltac rt_split := unfold mdtor_rt; repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Ltac lit_nat := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat (Zpos ?p)) _] |- _ =>
                  let small := eval vm_compute in (Pos.leb p 5000) in
                  lazymatch small with true => idtac end;          (* [comment removed for export] *)
                  let v := eval vm_compute in (Z.to_nat (Zpos p)) in change (Z.to_nat (Zpos p)) with v in H; move H at top end.
Ltac lit_addr := repeat match goal with H : rw_cells _ _ (Zpos ?a + Zpos ?b) _ |- _ =>
                  let v := eval vm_compute in (Zpos a + Zpos b) in change (Zpos a + Zpos b) with v in H end.
Ltac lit_rng := repeat match goal with H : rng _ _ (Zpos ?a - Zpos ?b) |- _ =>
                  let v := eval vm_compute in (Zpos a - Zpos b) in change (Zpos a - Zpos b) with v in H end.
(* [comment removed for export] *)
Ltac side RIMG RSTK KH :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia] ]
  | |- rng_aimg _ => exact RIMG
  | |- rw_cells _ _ (?a + ?b) _ => let v := eval vm_compute in (a + b) in change (a + b) with v; hyp_by_addr
  | |- rw_cells _ _ _ _ => hyp_by_addr
  | |- mdtor_rt _ => rt_split
  | |- mem_inv _ _ => hyp_by_addr
  | |- stk _ _ _ _ => hyp_by_addr
  | |- @eq _ _ _ => reflexivity
  | |- Z.lt (shn _) _ => vm_compute; reflexivity
  | |- _ => first [exact KH | lia]
  end.

Local Ltac clear_at a := try (match goal with H : rw_cells _ _ a _ |- _ => clear H end).
Definition parked (P : Prop) : Prop := P.
Local Ltac park H := lazymatch type of H with ?T => change T with (parked T) in H end.
Local Ltac unpark H MU WM DISJ :=
  unfold parked in H;
  lazymatch type of H with
  | rw_cells ?segs ?m0 ?a ?cs =>
      lazymatch type of MU with
      | munch ?W m0 ?m1 => apply (rw_cells_transport segs W m0 m1 a cs) in H; [ | exact MU | exact WM | apply DISJ; cbn; lia ]
      end
  end.
Section CANSEC3. Context {rc : runConstT}.
Theorem module_dtor_proof : module_dtor_stmt mdtor_pre.
Proof.
  unfold module_dtor_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW.
  pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold mdtor_pre, gdesc in P.
  destruct P as (RT & GSS & FLG & MTX & (D0 & B0) & (D1 & B1) & (D2 & B2) & (D3 & B3) & (D4 & B4) & (D5 & B5) & (D6 & B6) & (D7 & B7) & (D8 & B8) & (D9 & B9) & (D10 & B10) & (D11 & B11) & (D12 & B12) & (D13 & B13) & (D14 & B14) & (D15 & B15) & (D16 & B16) & (D17 & B17) & (D18 & B18) & (D19 & B19) & (D20 & B20) & (D21 & B21) & (D22 & B22) & (D23 & B23) & (D24 & B24) & (D25 & B25) & (D26 & B26) & (D27 & B27) & (D28 & B28) & (D29 & B29) & (D30 & B30) & (D31 & B31) & [j0 S0] & [j1 S1] & [j2 S2] & [j3 S3] & [j4 S4] & [j5 S5] & [j6 S6] & [j7 S7] & [j8 S8] & [j9 S9] & [j10 S10] & [j11 S11] & [j12 S12] & [j13 S13] & [j14 S14] & [j15 S15] & [j16 S16] & [j17 S17] & [j18 S18] & [j19 S19] & [j20 S20] & [j21 S21] & [j22 S22] & [j23 S23] & [j24 S24] & [j25 S25] & [j26 S26] & [j27 S27] & [j28 S28] & [j29 S29] & [j30 S30] & [j31 S31] & [j32 S32]).
  lit_addr.
  change (2^64 - 1) with 18446744073709551615 in D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22, D23, D24, D25, D26, D27, D28, D29, D30, D31.
  (* [comment removed for export] *)
  park D0; park B0. park D1; park B1. park D2; park B2. park D3; park B3. park D4; park B4. park D5; park B5. park D6; park B6. park D7; park B7. park D8; park B8. park D9; park B9. park D10; park B10. park D11; park B11. park D12; park B12. park D13; park B13. park D14; park B14. park D15; park B15. park D16; park B16. park D17; park B17. park D18; park B18. park D19; park B19. park D20; park B20. park D21; park B21. park D22; park B22. park D23; park B23. park D24; park B24. park D25; park B25. park D26; park B26. park D27; park B27. park D28; park B28. park D29; park B29. park D30; park B30. park D31; park B31.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  (* [comment removed for export] *)
  unfold MDTOR_W in RW.
  repeat lazymatch type of RW with Forall _ (_ :: _) =>
    let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
  lit_rng.
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0xd64c0, 0xd64c8); (0xd7430, 0xd7438); (0x7fffc4ec, 0x7fffc4f0); (0x7fffc508, 0x7fffca60); (0x7fffc5b4, 0x7fffc8d4); (0x7fffc8dc, 0x7fffc90c); (0x7fffca68, 0x7fffca80); (0x800b9840, 0x800c3840); (0x80012b98, 0x80012c98)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (DISJ : forall A n, 0 <= n -> 0xd5cc0 <= A -> A + n <= 0xd64c0 -> disjoint_from [(bv_unsigned sp - 1024, bv_unsigned sp); (0xd64c0, 0xd64c8); (0xd7430, 0xd7438); (0x7fffc4ec, 0x7fffc4f0); (0x7fffc508, 0x7fffca60); (0x7fffc5b4, 0x7fffc8d4); (0x7fffc8dc, 0x7fffc90c); (0x7fffca68, 0x7fffca80); (0x800b9840, 0x800c3840); (0x80012b98, 0x80012c98)]%Z A n).
  { intros A n Hn HA HB. cbn [disjoint_from fst snd]. repeat split; lia. }
  (* [comment removed for export] *)
  assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
  sort_lits. move S0 at top. move S1 at top. move S2 at top. move S3 at top. move S4 at top. move S5 at top. move S6 at top. move S7 at top. move S8 at top. move S9 at top. move S10 at top. move S11 at top. move S12 at top. move S13 at top. move S14 at top. move S15 at top. move S16 at top. move S17 at top. move S18 at top. move S19 at top. move S20 at top. move S21 at top. move S22 at top. move S23 at top. move S24 at top. move S25 at top. move S26 at top. move S27 at top. move S28 at top. move S29 at top. move S30 at top. move S31 at top. move S32 at top.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 9 hstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 hstep. astep. hstep. hstep. astep. do 2 hstep. astep. do 4 hstep.
  (* [comment removed for export] *)
  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.                                          (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  steps_to 0x4b1e8%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hstep. hstep. astep.
  steps_to 0x4b2fc%Z.
  (* [comment removed for export] *)
  unpark D0 MU WM DISJ; unpark B0 MU WM DISJ. move D0 after REAL. move B0 after D0.
  assert (RX : rng RNG 0x7fffc4ec 4) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc4ec 4 0x7fffc4f0). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc4ec.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5cc0; clear_at 0xd5cd0.          (* [comment removed for export] *)
  unpark D1 MU WM DISJ; unpark B1 MU WM DISJ. move D1 after REAL. move B1 after D1.
  assert (RX : rng RNG 0x7fffc508 12) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc508 12 0x7fffc514). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc508.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5d00; clear_at 0xd5d10.          (* [comment removed for export] *)
  unpark D2 MU WM DISJ; unpark B2 MU WM DISJ. move D2 after REAL. move B2 after D2.
  assert (RX : rng RNG 0x7fffc514 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc514 8 0x7fffc51c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc514.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5d40; clear_at 0xd5d50.          (* [comment removed for export] *)
  unpark D3 MU WM DISJ; unpark B3 MU WM DISJ. move D3 after REAL. move B3 after D3.
  assert (RX : rng RNG 0x7fffc51c 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc51c 8 0x7fffc524). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc51c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5d80; clear_at 0xd5d90.          (* [comment removed for export] *)
  unpark D4 MU WM DISJ; unpark B4 MU WM DISJ. move D4 after REAL. move B4 after D4.
  assert (RX : rng RNG 0x7fffc524 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc524 8 0x7fffc52c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc524.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5dc0; clear_at 0xd5dd0.          (* [comment removed for export] *)
  unpark D5 MU WM DISJ; unpark B5 MU WM DISJ. move D5 after REAL. move B5 after D5.
  assert (RX : rng RNG 0x7fffc52c 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc52c 8 0x7fffc534). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc52c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5e00; clear_at 0xd5e10.          (* [comment removed for export] *)
  unpark D6 MU WM DISJ; unpark B6 MU WM DISJ. move D6 after REAL. move B6 after D6.
  assert (RX : rng RNG 0x7fffc534 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc534 8 0x7fffc53c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc534.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5e40; clear_at 0xd5e50.          (* [comment removed for export] *)
  unpark D7 MU WM DISJ; unpark B7 MU WM DISJ. move D7 after REAL. move B7 after D7.
  assert (RX : rng RNG 0x7fffc53c 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc53c 8 0x7fffc544). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc53c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5e80; clear_at 0xd5e90.          (* [comment removed for export] *)
  unpark D8 MU WM DISJ; unpark B8 MU WM DISJ. move D8 after REAL. move B8 after D8.
  assert (RX : rng RNG 0x7fffc544 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc544 8 0x7fffc54c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc544.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5ec0; clear_at 0xd5ed0.          (* [comment removed for export] *)
  unpark D9 MU WM DISJ; unpark B9 MU WM DISJ. move D9 after REAL. move B9 after D9.
  assert (RX : rng RNG 0x7fffc54c 12) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc54c 12 0x7fffc558). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc54c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5f00; clear_at 0xd5f10.          (* [comment removed for export] *)
  unpark D10 MU WM DISJ; unpark B10 MU WM DISJ. move D10 after REAL. move B10 after D10.
  assert (RX : rng RNG 0x7fffc558 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc558 8 0x7fffc560). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc558.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5f40; clear_at 0xd5f50.          (* [comment removed for export] *)
  unpark D11 MU WM DISJ; unpark B11 MU WM DISJ. move D11 after REAL. move B11 after D11.
  assert (RX : rng RNG 0x7fffc560 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc560 8 0x7fffc568). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc560.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5f80; clear_at 0xd5f90.          (* [comment removed for export] *)
  unpark D12 MU WM DISJ; unpark B12 MU WM DISJ. move D12 after REAL. move B12 after D12.
  assert (RX : rng RNG 0x7fffc568 12) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc568 12 0x7fffc574). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc568.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd5fc0; clear_at 0xd5fd0.          (* [comment removed for export] *)
  unpark D13 MU WM DISJ; unpark B13 MU WM DISJ. move D13 after REAL. move B13 after D13.
  assert (RX : rng RNG 0x7fffc574 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc574 8 0x7fffc57c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc574.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6000; clear_at 0xd6010.          (* [comment removed for export] *)
  unpark D14 MU WM DISJ; unpark B14 MU WM DISJ. move D14 after REAL. move B14 after D14.
  assert (RX : rng RNG 0x7fffc57c 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc57c 8 0x7fffc584). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc57c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6040; clear_at 0xd6050.          (* [comment removed for export] *)
  unpark D15 MU WM DISJ; unpark B15 MU WM DISJ. move D15 after REAL. move B15 after D15.
  assert (RX : rng RNG 0x7fffc584 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc584 8 0x7fffc58c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc584.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6080; clear_at 0xd6090.          (* [comment removed for export] *)
  unpark D16 MU WM DISJ; unpark B16 MU WM DISJ. move D16 after REAL. move B16 after D16.
  assert (RX : rng RNG 0x7fffc58c 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc58c 8 0x7fffc594). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc58c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd60c0; clear_at 0xd60d0.          (* [comment removed for export] *)
  unpark D17 MU WM DISJ; unpark B17 MU WM DISJ. move D17 after REAL. move B17 after D17.
  assert (RX : rng RNG 0x7fffc594 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc594 8 0x7fffc59c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc594.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6100; clear_at 0xd6110.          (* [comment removed for export] *)
  unpark D18 MU WM DISJ; unpark B18 MU WM DISJ. move D18 after REAL. move B18 after D18.
  assert (RX : rng RNG 0x7fffc59c 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc59c 8 0x7fffc5a4). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc59c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6140; clear_at 0xd6150.          (* [comment removed for export] *)
  unpark D19 MU WM DISJ; unpark B19 MU WM DISJ. move D19 after REAL. move B19 after D19.
  assert (RX : rng RNG 0x7fffc5a4 8) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc5a4 8 0x7fffc5ac). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc5a4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6180; clear_at 0xd6190.          (* [comment removed for export] *)
  unpark D20 MU WM DISJ; unpark B20 MU WM DISJ. move D20 after REAL. move B20 after D20.
  assert (RX : rng RNG 0x7fffc5b4 160) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc5b4 160 0x7fffc654). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc5b4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd61c0; clear_at 0xd61d0.          (* [comment removed for export] *)
  unpark D21 MU WM DISJ; unpark B21 MU WM DISJ. move D21 after REAL. move B21 after D21.
  assert (RX : rng RNG 0x7fffc654 640) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc654 640 0x7fffc8d4). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc654.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6200; clear_at 0xd6210.          (* [comment removed for export] *)
  unpark D22 MU WM DISJ; unpark B22 MU WM DISJ. move D22 after REAL. move B22 after D22.
  assert (RX : rng RNG 0x7fffc8dc 12) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc8dc 12 0x7fffc8e8). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc8dc.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6240; clear_at 0xd6250.          (* [comment removed for export] *)
  unpark D23 MU WM DISJ; unpark B23 MU WM DISJ. move D23 after REAL. move B23 after D23.
  assert (RX : rng RNG 0x7fffc8e8 12) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc8e8 12 0x7fffc8f4). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc8e8.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6280; clear_at 0xd6290.          (* [comment removed for export] *)
  unpark D24 MU WM DISJ; unpark B24 MU WM DISJ. move D24 after REAL. move B24 after D24.
  assert (RX : rng RNG 0x7fffc8f4 12) by (apply (rng_sub' _ _ _ _ _ RW5); lia).
  call (unreg_one_spec RNG 0x7fffc8f4 12 0x7fffc900). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc8f4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd62c0; clear_at 0xd62d0.          (* [comment removed for export] *)
  unpark D25 MU WM DISJ; unpark B25 MU WM DISJ. move D25 after REAL. move B25 after D25.
  assert (RX : rng RNG 0x7fffc900 12) by (apply (rng_sub' _ _ _ _ _ RW5); lia).
  call (unreg_one_spec RNG 0x7fffc900 12 0x7fffc90c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc900.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6300; clear_at 0xd6310.          (* [comment removed for export] *)
  unpark D26 MU WM DISJ; unpark B26 MU WM DISJ. move D26 after REAL. move B26 after D26.
  assert (RX : rng RNG 0x7fffc90c 320) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc90c 320 0x7fffca4c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc90c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6340; clear_at 0xd6350.          (* [comment removed for export] *)
  unpark D27 MU WM DISJ; unpark B27 MU WM DISJ. move D27 after REAL. move B27 after D27.
  assert (RX : rng RNG 0x7fffca4c 20) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffca4c 20 0x7fffca60). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffca4c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6380; clear_at 0xd6390.          (* [comment removed for export] *)
  unpark D28 MU WM DISJ; unpark B28 MU WM DISJ. move D28 after REAL. move B28 after D28.
  assert (RX : rng RNG 0x7fffca68 8) by (apply (rng_sub' _ _ _ _ _ RW6); lia).
  call (unreg_one_spec RNG 0x7fffca68 8 0x7fffca70). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffca68.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd63c0; clear_at 0xd63d0.          (* [comment removed for export] *)
  unpark D29 MU WM DISJ; unpark B29 MU WM DISJ. move D29 after REAL. move B29 after D29.
  assert (RX : rng RNG 0x7fffca70 8) by (apply (rng_sub' _ _ _ _ _ RW6); lia).
  call (unreg_one_spec RNG 0x7fffca70 8 0x7fffca78). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffca70.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6400; clear_at 0xd6410.          (* [comment removed for export] *)
  unpark D30 MU WM DISJ; unpark B30 MU WM DISJ. move D30 after REAL. move B30 after D30.
  assert (RX : rng RNG 0x7fffca78 8) by (apply (rng_sub' _ _ _ _ _ RW6); lia).
  call (unreg_one_spec RNG 0x7fffca78 8 0x7fffca80). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffca78.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6440; clear_at 0xd6450.          (* [comment removed for export] *)
  unpark D31 MU WM DISJ; unpark B31 MU WM DISJ. move D31 after REAL. move B31 after D31.
  assert (RX : rng RNG 0x800b9840 40960) by (apply (rng_sub' _ _ _ _ _ RW7); lia).
  call (unreg_one_spec RNG 0x800b9840 40960 0x800c3840). all: side RIMG RSTK KH. clear RX. clear_at 0x800b9840.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0xd6480; clear_at 0xd6490.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  steps_to 0x4b518%Z. hstep.                            (* [comment removed for export] *)
  move RW8 at bottom.
  call_sp (poison_low_spec RNG 0x80012b98 256). all: side RIMG RSTK KH. clear RW8.
  lit_nat.
  (* [comment removed for export] *)
  steps_to 0x4b558%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.                                               (* [comment removed for export] *)
  steps_to 0x4b7b0%Z.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32) end.
  hstep. hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16) end.
  hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  hstep.
  unfold module_dtor_post. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Closed.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  (* [comment removed for export] *)
  Definition aexit_spec_closed (FOE : funcs_on_exit_specA_stmt) :=
    aexit_spec get_so set_so mdtor_pre module_dtor_proof mdtor_pre_frame FOE
               (F_stdio_exit.stdio_exit_proof get_so set_so get_set set_set set_get).
End Closed.
End CANSEC3.
