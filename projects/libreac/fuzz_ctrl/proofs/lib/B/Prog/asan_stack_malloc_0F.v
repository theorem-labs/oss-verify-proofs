(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/As/AllocWalkKit.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Tk/AW/SmLeaf.v, with its module paths, module names and numbers changed; 359 of its 393 lines of code are new or changed and 353 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Tk/AW/Sm6.v, with its module paths, module names and numbers changed; 131 of its 252 lines of code are new or changed and 272 lines of the source are left out. *)
(* lib/B/Prog/asan_stack_malloc_0F.v -- fuzz_ctrl image B (asan-ubsan): __asan_stack_malloc_0 (0x3d6f4) in footprint
   form.  asan_stack_malloc_0_holds_F_on proves asan_stack_malloc_0_contract_F_on (asan_stack_malloc_cF_on.v) by the
   walk; asan_stack_malloc_0_holds_F proves asan_stack_malloc_0_contract_F (asan_stack_malloc_cF.v) by that file's
   bridge asan_stack_malloc_contract_F_of_F_on.  Neither statement is changed here.
   rule 24: no function proved for the first time.  fuzz_grant proves this walk at the footprint level.

   DONOR.  a working branch dac1040b24ec, proofs/libreac/fuzz_grant/lib/B/Prog/asan_stack_mallocF.v:
   rng_sh_frame0 (lines 166-178), Section LoopF0 / probeF0 (664-721) and asan_stack_malloc_0_holds_Fcan (841-1015),
   itself relocated from fuzz_pcap lib/B/Prog/asan_stack_malloc_0F.v at 78bd0706625 (the donor's header, lines
   19-23).  The class-independent part (cell helpers, TLS callees, MemToShadow) is this unit's
   asan_stack_mallocF_kit.v (same donor, lines 53-165 and 202-662).

   STATEMENTS.  The donor proves grant's asan_stack_malloc_0_contract_Fcan (asan_stack_mallocF_c.v at dac1040b24ec).
   This unit's asan_stack_malloc_contract_F_on has the same premises and post, in the same order, except:
   - shadow: `shadow_rw m` is `shadow_rw_on (asan_stack_malloc_shadow_R FS 0) m` (asan_stack_malloc_c_on.v);
   - side stack: in place of grant's single `rng RNG FS FS_SIZE` it has two regions, the header
     `rng RNG FS (fs_frame FS 0 0 - FS)` and the class-0 frame area `rng RNG (fs_frame FS 0 0) (2 ^ 20)`;
   - the image range is ImgBounds.v's [IMG_LO, IMG_HI) = [0x10000, 0x5fe000) (grant: [0x10000, 0x5fb000)).
   asan_stack_malloc_contract_F differs from _F_on only by `shadow_rw m` (asan_stack_malloc_cF_on.v header).

   CHANGES to the donor's text, and nothing else:
   - the namespace fuzz_grant -> fuzz_ctrl; the imports (this unit's statement files and the kit in place of grant's
     asan_stack_mallocF_c.v); `Local Unset` for the three Lia/Nia/Nra cache options (settings v10);
   - the names: asan_stack_malloc_0_holds_Fcan -> asan_stack_malloc_0_holds_F_on (and its unfold line);
   - the side-stack region: the walk's intro RFS becomes RFH RFA; three lines after the intros rewrite
     fs_frame FS 0 0 = FS + 36864 (E00) in both and close them to rng RNG FS 36864 and rng RNG (FS + 36864) 1048576.
     The run's side-stack accesses each lie in one of them: the hint word [FS, FS + 8) (load at 0x3d754, store at
     0x3d800 or, all frames used, 0x3d794), the words at FS + 88 (0x3d724) and FS + 96 (0x3d720), the flag byte
     FS + 4096 + pos, pos < 16384
     (load 0x3d780, store 0x3d804) are in the header; the frame words Fa + 24 (0x3d814) and Fa + 56 (0x3d818),
     Fa = FS + 36864 + 64 pos, are in the frame area.  LoopF0's section hypothesis RFS : rng RNG FS 11571200 is
     RFH : rng RNG FS 36864 (the loop reads flag bytes only);
   - the shadow: SHS (the 131072 shadow bytes from shadow_addr (FS + 36864) are present) comes from the kit's
     shadow_stk_on with the statement's region, in place of SmLib.shadow_stk with shadow_rw.  The run's only shadow
     access is the 8-byte store `sd zero, 0(a1)` at 0x3d830 to SA = shadow_addr Fa = shadow_addr (FS + 36864) + 8 pos,
     inside asan_stack_malloc_shadow_R FS 0 = [shadow_addr (fs_frame FS 0 0), + 131072) as pos < 16384; the
     callees load no shadow byte (the run has FS + 96 = 0, so FakeStack::GC at 0x3d2a8 is not called: the beqz at
     0x3d728);
   - rng_sh_frame0: `rewrite (fs_shadow_area_small 0 ...)` (grant's asan_stackmallocF_c.v lemma, absent here) is
     `change (fs_shadow_area 0) with 131072`, by computation;
   - relocated numerals (the same symbol + offset in grant's and this unit's asan-ubsan image of libreac v1.9.0,
     (internal path) sha256 ee07e2c38d94...; the function's code is the same
     modulo pc-relative fields, EQUAL-mod-pcrel by comparison kit 86da41d3ef68, strictcmp3 65688e94214a):
       0x3cf4c -> 0x3d6f4 __asan_stack_malloc_0 + 0     0x3cf70 -> 0x3d718 + 0x24 (return of the interceptor call)
       0x3cfd0 -> 0x3d778 + 0x84 (probe loop head)     0x3cfec -> 0x3d794 + 0xa0 (all frames used)
       0x3d048 -> 0x3d7f0 + 0xfc (free frame found)     0x5fb000 -> 0x5fe000 the image top (ASAN_GT, IMG_HI; no symbol)
   - the _F shape: by the bridge asan_stack_malloc_contract_F_of_F_on of asan_stack_malloc_cF_on.v, in place of the
     donor's asan_stack_malloc_0_contract_F_of_Fcan (donor line 1369-1370). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLeaf SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c rng_asan
  asan_stack_malloc_c_on asan_stack_malloc_cF asan_stack_malloc_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_mallocF_kit.
Local Unset Lia Cache. Local Unset Nia Cache. Local Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* The 8 shadow bytes of frame j of the class-0 frame area (fs_frame FS 0 j = FS + 36864 + 64 j, j < fs_M 0 = 16384)
   lie in the shadow range of that area, the frame-shadow premise of asan_stack_malloc_contract_F
   and _F_on (asan_stack_malloc_cF.v, asan_stack_malloc_cF_on.v): [shadow_addr (FS + 36864) + 8 j, + 8) inside 2^17 bytes from shadow_addr (FS + 36864). *)
Lemma rng_sh_frame0 : forall RNG FS j, rng RNG (shadow_addr (fs_frame FS 0 0)) (fs_shadow_area 0) ->
  0 <= j < 16384 -> rng RNG (shadow_addr (FS + 36864 + j * 64)) 8.
Proof.
  intros RNG FS j H Hj.
  replace (fs_frame FS 0 0) with (FS + 36864) in H
    by (unfold fs_frame; replace (Z.of_nat 0) with 0 by reflexivity; replace (0 * fs_B 0) with 0 by ring; lia).
  change (fs_shadow_area 0) with 131072 in H.
  replace (FS + 36864 + j * 64) with (FS + 36864 + 8 * (8 * j)) by lia.
  rewrite shadow_addr_add. apply (rng_sub RNG _ _ _ _ H); lia.
Qed.

(* ------------------------------------------------------------------ the probe loop (0x3d778)

   The walk of lib/B/Tk/AW/Sm0.v's [probe] as a footprint run: from the loop head with the counter at 16384 - i and
   the probe at h + i, the run reads flag bytes until the first free one (KF) or until the counter runs out (KE). *)

Section LoopF0.
  Variables (RNG : footprint) (sp gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (FS hZ : Z) (flags : list byte)
    (Q : machine_state -> Prop).
  Hypothesis FS0 : 0 < FS.
  Hypothesis FSB : FS + 11571200 <= 2 ^ 64.
  Hypothesis HR : 0 <= hZ < 2 ^ 64.
  Hypothesis FLB : bytes_at rsegs m (FS + 4096) flags.
  Hypothesis FLEN : Z.of_nat (length flags) = 16384.
  Hypothesis F01 : Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags.
  Hypothesis RIMG : rng RNG IMG_LO (IMG_HI - IMG_LO).
  Hypothesis RFH : rng RNG FS 36864.
  Abbreviation LS pc x10 x12 x15 x16 x17 :=
    (MS (mkR (Z_to_bv 64 0x3d718) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 FS)
             x10 (Z_to_bv 64 (FS + 4096)) x12 (Z_to_bv 64 16383) (Z_to_bv 64 (hZ + 16384)) x15 x16 x17
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Hypothesis KF : forall j (x17 : word), 0 <= j < 16384 ->
    (forall i', 0 <= i' < j -> nth_error flags (Z.to_nat ((hZ + i') mod 16384)) = Some (Z_to_bv 8 1)) ->
    nth_error flags (Z.to_nat ((hZ + j) mod 16384)) = Some (Z_to_bv 8 0) ->
    evtF rsegs RNG Q (LS 0x3d7f0 (Z_to_bv 64 (16384 - j)) (Z_to_bv 64 (hZ + j))
                   (Z_to_bv 64 (FS + 4096 + (hZ + j) mod 16384)) (Z_to_bv 64 ((hZ + j) mod 16384)) x17).
  Hypothesis KE : forall (x12 x15 x16 x17 : word),
    (forall i', 0 <= i' < 16384 -> nth_error flags (Z.to_nat ((hZ + i') mod 16384)) = Some (Z_to_bv 8 1)) ->
    evtF rsegs RNG Q (LS 0x3d794 (Z_to_bv 64 0) x12 x15 x16 x17).

  Lemma probeF0 (k : nat) : forall i (x15 x16 x17 : word),
    Z.to_nat (16384 - i) = k -> 0 <= i < 16384 ->
    (forall i', 0 <= i' < i -> nth_error flags (Z.to_nat ((hZ + i') mod 16384)) = Some (Z_to_bv 8 1)) ->
    evtF rsegs RNG Q (LS 0x3d778 (Z_to_bv 64 (16384 - i)) (Z_to_bv 64 (hZ + i)) x15 x16 x17).
  Proof using FS0 FSB HR FLB FLEN F01 KF KE RIMG RFH.
    img_rng RIMG.
    induction k as [|k IH]; intros i x15 x16 x17 Hk Hi ONES; [lia|].
    assert (PR : 0 <= (hZ + i) mod 16384 < 16384) by (apply Z.mod_pos_bound; lia).
    destruct (flag_readF m (FS + 4096) flags ((hZ + i) mod 16384) FLB ltac:(lia) F01) as (b & NTH & B01 & RD).
    zstep. rewrite (land_mod_low _ 14 16383 16384) by first [reflexivity | lia].
    zstep.
    destruct B01 as [-> | ->].
    - zstep. try change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_true.
      apply KF; [lia| exact ONES| exact NTH].
    - zstep. try change (bv_unsigned (Z_to_bv 8 1)) with 1.
      zstep. if_false.
      zstep. rewrite swrap32_smallF by lia.
      zstep. zstep. if_cases K; zify_cond K.
      + assert (Hi1 : i + 1 < 16384) by (first [lia | rewrite Z.mod_small in K by lia; lia]).
        replace (16384 - i + -1) with (16384 - (i + 1)) by lia. replace (hZ + i + 1) with (hZ + (i + 1)) by lia.
        apply IH; [lia| lia|]. intros i' Hi'. destruct (Z.eq_dec i' i) as [->|NE]; [exact NTH| apply ONES; lia].
      + assert (Hi1 : i = 16383) by (first [lia | rewrite Z.mod_small in K by lia; lia]).
        replace (16384 - i + -1) with 0 by lia.
        apply KE. intros i' Hi'. destruct (Z.eq_dec i' i) as [->|NE]; [exact NTH| apply ONES; lia].
  Qed.
End LoopF0.

(* ------------------------------------------------------------------ __asan_stack_malloc_0 (0x3d6f4) *)

Theorem asan_stack_malloc_0_holds_F_on : asan_stack_malloc_0_contract_F_on.
Proof.
  unfold asan_stack_malloc_0_contract_F_on, asan_stack_malloc_contract_F_on, ASAN_STACK_MALLOC_0, ASAN_STACK_MALLOC_K.
  cbv zeta.
  intros _CLS RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo FS h DT TS C T DB k flags.
  intros HL HL8 AC SRW MI0 TLS _ FSP PL SSL0 GC0 HINT0 FLG0 FLEN F01 ST0 LOK ROOM APS DISJ.
  intros RIMG0 RFR RDT RTS RCX RT48 RDB RFH RFA RSH RTP88 RTPW.
  (* The side-stack regions of the statement as closed forms: the header [FS, FS + 36864) and the class-0 frame
     area [FS + 36864, FS + 36864 + 2^20). *)
  assert (E00 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  rewrite E00 in RFH, RFA. replace (FS + 36864 - FS) with 36864 in RFH by lia. change (2 ^ 20) with 1048576 in RFA.
  (* The no-wrap bounds of the thread cells: each cell's bytes_at fact in asan_tls_cells carries 0 <= A and
     A + 8 <= 2^64 (the same derivations as asan_stack_malloc_contract_on_of_F_on, asan_stack_malloc_cF_on.v). *)
  pose proof TLS as TLSc.
  destruct TLSc as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
                    & A18 & A19).
  assert (TPLO : 88 <= bv_unsigned tp) by (destruct A8 as (Ha & _); lia).
  assert (TPHI : bv_unsigned tp + 16 <= 2 ^ 64)
    by (destruct A17 as (_ & Hb & _); rewrite length_le8 in Hb; lia).
  assert (DTHI : bv_unsigned DT + 16 <= 2 ^ 64)
    by (destruct A4 as (_ & Hb & _); rewrite length_le8 in Hb; lia).
  assert (TSHI : bv_unsigned TS + 8 * k + 8 <= 2 ^ 64)
    by (destruct A9 as (_ & Hb & _); rewrite length_le8 in Hb; lia).
  assert (CHI : bv_unsigned C + 160 <= 2 ^ 64)
    by (destruct A10 as (_ & Hb & _); rewrite length_le8 in Hb; lia).
  assert (THI : bv_unsigned T + 64 <= 2 ^ 64)
    by (destruct A11 as (tb0 & te0 & (_ & Hb & _)); rewrite length_app, !length_le8 in Hb; lia).
  assert (DBHI : bv_unsigned DB + 32 <= 2 ^ 64)
    by (destruct A19 as (_ & Hb & _); rewrite length_le8 in Hb; lia).
  clear A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19.
  rename RIMG0 into RIMG.
  assert (LRNG : leaf_rng RNG (bv_unsigned tp) (bv_unsigned DT) (bv_unsigned TS) (bv_unsigned C) (bv_unsigned T)
                   (bv_unsigned DB) k)
    by exact (conj RIMG (conj RTP88 (conj RTPW (conj RDT (conj RTS (conj RCX (conj RT48 RDB))))))).
  img_rng RIMG.
  destruct (tls_leafF m (bv_unsigned tp) DT TS C T DB k AC TLS) as (tb & te & LC).
  pose proof (m2s_of_asanF m AC) as M2. clear AC TLS.
  destruct PL as (FS0 & FS4K & FSGT & FAPP & FSTK0).
  assert (STF : stk rsegs m FS (FS + FS_SIZE)) by exact FSTK0. clear FSTK0.
  assert (ST : stk rsegs m lo (bv_unsigned sp)) by exact ST0. clear ST0.
  assert (MI : mem_inv rsegs m) by exact MI0. clear MI0.
  assert (TPE : tp = Z_to_bv 64 (bv_unsigned tp)) by (symmetry; apply Z_to_bv_lit_self).
  assert (AP : leaf_apartF (bv_unsigned tp) (bv_unsigned DT) (bv_unsigned TS) (bv_unsigned C) (bv_unsigned T)
                 (bv_unsigned DB) k (bv_unsigned sp - 208) (bv_unsigned sp)).
  { split; [unfold FS_SIZE, ASAN_GT in *; lia|]. split; [lia|].
    split; [pose proof (bv_unsigned_in_range 64 sp) as R; unfold bv_modulus in R; cbn in R; lia|].
    replace (bv_unsigned sp - (bv_unsigned sp - 208)) with 208 by lia. exact DISJ. }
  clear DISJ.
  pose proof AP as (_ & _ & _ & DJ). unfold leaf_ivsF in DJ. cbn [disjoint_from] in DJ.
  destruct DJ as (DJ1 & DJ2 & DJ3 & DJ4 & DJ5 & DJ6 & DJ7 & _).
  assert (TPC : ro_cells rsegs m (bv_unsigned tp) [C8 (Z_to_bv 64 FS)]) by (apply ro8F; exact FSP). clear FSP.
  assert (SSL : ro_cells rsegs m (FS + 88) [C8 (Z_to_bv 64 20)]) by (apply ro8F; exact SSL0). clear SSL0.
  assert (GCC : ro_cells rsegs m (FS + 96) [C1 (Z_to_bv 8 0)]) by (apply ro1F; exact GC0). clear GC0.
  replace (fs_hint FS 0) with FS in HINT0 by (unfold fs_hint; simpl; lia).
  rewrite <- (Z_to_bv_lit_self h) in HINT0.
  assert (HN : rw_cells rsegs m FS [C8 (Z_to_bv 64 (bv_unsigned h))]).
  { apply (stk_rwF m FS (FS + FS_SIZE)); [exact STF| apply ro8F; exact HINT0| lia| cbn; unfold FS_SIZE; lia]. }
  clear HINT0.
  replace (fs_flag FS 0 0) with (FS + 4096) in FLG0 by (unfold fs_flag; simpl; lia).
  assert (FLB : bytes_at rsegs m (FS + 4096) flags) by exact FLG0. clear FLG0.
  change (fs_M 0) with 16384 in FLEN.
  remember (shadow_addr (FS + 36864)) as SB eqn:ESB.
  assert (SHS : stk rsegs m SB (SB + 131072)).
  { subst SB. apply (shadow_stk_on m (asan_stack_malloc_shadow_R FS 0)); [exact SRW| | lia| unfold FS_SIZE in *; lia| lia|].
    - intros y Hy. unfold asan_stack_malloc_shadow_R. rewrite E00. exact Hy.
    - intros x Hx. apply FAPP. unfold FS_SIZE. lia. }
  assert (SHI : forall y, SB <= y < SB + 131072 -> in_shadow y).
  { subst SB. apply shadow_range_in; [lia| lia| lia|]. intros x Hx. apply FAPP. unfold FS_SIZE. lia. }
  assert (DSH : bv_unsigned sp <= SB \/ SB + 131072 <= bv_unsigned sp - 208).
  { apply (app_shadow_apart (bv_unsigned sp - 208) (bv_unsigned sp) SB 131072); [exact APS| lia| exact SHI| lia]. }
  pose proof (bv_unsigned_in_range 64 h) as HR. unfold bv_modulus in HR. cbn in HR.
  remember (bv_unsigned h) as hZ eqn:EhZ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold FS_SIZE, ASAN_GT in *.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 32%nat ST. do 4 zstep. zstep.
  do 2 zstep.
  freshLCF LC0.
  zstep. call_sp icptF_spec;
    first [ exact ST | reflexivity | exact TPE | exact LC0 | exact LRNG
          | eapply leaf_apart_subF; [exact AP| lia ..] | solve_rng | lia | assumption | idtac ].
  rename POST into ST. clear LC0.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; first [lia | rewrite Z.mod_small in K0 by lia; lia]|].
  zstep. zstep. zstep. if_true.
  zstep. zstep. zstep. zstep.
  zstep. if_false.
  do 11 zstep.
  replace (Z_to_bv 64 hZ) with (Z_to_bv 64 (hZ + 0)) by (rewrite Z.add_0_r; reflexivity).
  assert (DFS : FS + 11571200 <= SB \/ SB + 131072 <= FS)
    by (apply (app_shadow_apart FS (FS + 11571200) SB 131072); [exact FAPP| lia| exact SHI| lia]).
  clear DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 DJ7 TPC K0.
  refine (probeF0 RNG sp gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mA FS hZ flags _
            ltac:(lia) ltac:(lia) HR FLB FLEN F01 RIMG RFH _ _ _ 0 _ _ _ eq_refl ltac:(lia) ltac:(intros; lia)).
  - intros j x17 Hj ONES ZERO.
    assert (HP : 0 <= (hZ + j) mod 16384 < 16384) by (apply Z.mod_pos_bound; lia).
    remember ((hZ + j) mod 16384) as pos eqn:Epos.
    pose proof (bytes_at_one mA _ _ _ _ FLB ZERO) as FB. rewrite Z2Nat.id in FB by lia.
    assert (FC : rw_cells rsegs mA (FS + 4096 + pos) [C1 (Z_to_bv 8 0)])
      by (apply (stk_rwF mA FS (FS + 11571200)); [exact STF| apply ro1F; exact FB| lia| cbn; lia]).
    clear FB.
    remember (FS + 4096 + pos) as FLG eqn:EFLG.
    remember (FS + 36864 + pos * 64) as Fa eqn:EFa.
    destruct (stk_junkF mA FS (FS + 11571200) (Fa + 24) 8 STF ltac:(lia) ltac:(lia)) as (j1 & FA1).
    destruct (stk_junkF mA FS (FS + 11571200) (Fa + 56) 8 STF ltac:(lia) ltac:(lia)) as (j2 & FA2).
    assert (ESA : shadow_addr Fa = SB + 8 * pos).
    { rewrite EFa, ESB. replace (FS + 36864 + pos * 64) with (FS + 36864 + 8 * (8 * pos)) by lia.
      apply shadow_addr_add. }
    assert (RSA : rng RNG (shadow_addr Fa) 8) by (rewrite EFa; exact (rng_sh_frame0 RNG FS pos RSH HP)).
    remember (shadow_addr Fa) as SA eqn:ESA'.
    destruct (stk_junkF mA SB (SB + 131072) SA 8 SHS ltac:(lia) ltac:(lia)) as (j3 & SHC).
    assert (SAL : 0x5fe000 <= SA).
    { pose proof (SHI SA ltac:(lia)) as X.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
    apply (munch_weaken _ [(FS, FS + 8); (FLG, FLG + 1); (Fa + 24, Fa + 32); (Fa + 56, Fa + 64);
                           (SA, SA + 8); (bv_unsigned sp - 208, bv_unsigned sp)]) in MU;
      [| unfold sub_fp; cbn [outside]; intros; tauto].
    do 4 zstep.
    zstep.
    zstep.
    do 3 zstep.
    match goal with |- context [Z_to_bv 64 ?e] => lazymatch e with context [Z.shiftl pos 6] =>
      replace e with Fa by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 6) with 64; lia) end end.
    zstep.
    zstep.
    zstep.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (m2s_cells_munchF m mx _ M2 MU ltac:(repeat constructor; cbn [fst]; lia)) as M2c end.
    zstep. call m2sF_spec;
      first [ reflexivity
            | (pose proof (FAPP Fa ltac:(lia)) as AF; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF;
               exact AF)
            | exact M2c | exact RIMG | assumption | idtac ].
    clear M2c.
    do 3 zstep.
    replace (Fa / 8 + 2147450880) with SA by (rewrite ESA'; reflexivity).
    zstep.
    do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evtF_done. subst hZ.
    assert (EFR : fs_frame FS 0 pos = Fa).
    { rewrite EFa. unfold fs_frame, fs_B.
      change (FS + 36864 + Z.of_nat 0 * 2 ^ 20 + pos * (64 * 2 ^ Z.of_nat 0)) with (FS + 36864 + 0 * 1048576 + pos * (64 * 1)).
      lia. }
    assert (EFG : fs_flag FS 0 pos = FLG).
    { rewrite EFLG. unfold fs_flag.
      change (FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat 0) + pos) with (FS + 4096 + 32768 - 32768 + pos). lia. }
    eapply (post_found 0 208 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) FS h flags lo m mF j);
      [exact WM| exact MI| exact ST| exact FS0| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
      | unfold FS_SIZE; exact STF| | change (fs_M 0) with 16384; lia| change (fs_M 0) with 16384; exact ONES
      | change (fs_M 0) with 16384; rewrite <- Epos; exact ZERO| ].
    + replace (fs_hint FS 0) with FS by (unfold fs_hint; simpl; lia). apply rw_c8_bytesF. exact HN.
    + change (fs_M 0) with 16384. rewrite <- Epos, <- EFR.
      apply frame_ok; [lia| change (fs_M 0) with 16384; lia| exact HL| exact FS4K| unfold ASAN_GT; lia
                     | unfold FS_SIZE; exact FAPP| unfold FS_SIZE; exact STF| unfold FS_SIZE; lia| | | | | ];
        rewrite ?EFR, ?EFG; try change (fs_B 0) with 64.
      * apply rw_c1_bytesF. exact FC.
      * apply rw_c8_bytesF. exact FA1.
      * replace (Fa + 64 - 8) with (Fa + 56) by lia. apply rw_c8_bytesF. exact FA2.
      * rewrite <- ESA'. change (Z.to_nat (64 / 8)) with 8%nat. rewrite <- le8_zeroF. apply rw_c8_bytesF. exact SHC.
      * rewrite <- ESA'. change (64 / 8) with 8. replace (fs_hint FS 0) with FS by (unfold fs_hint; simpl; lia).
        replace (Fa + 64 - 8) with (Fa + 56) by lia. exact MU.
  - intros x12 x15 x16 x17 ONES.
    apply (munch_weaken _ [(FS, FS + 8); (bv_unsigned sp - 208, bv_unsigned sp)]) in MU;
      [| unfold sub_fp; cbn [outside]; intros; tauto].
    zstep. zstep.
    do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evtF_done. subst hZ.
    eapply (post_full 0 208 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) FS h flags lo m mF);
      [exact WM| assumption| exact ST| exact FS0| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
      | unfold FS_SIZE; exact STF| | change (fs_M 0) with 16384; lia| change (fs_M 0) with 16384; exact FLEN
      | change (fs_M 0) with 16384; exact ONES| ].
    + replace (fs_hint FS 0) with FS by (unfold fs_hint; simpl; lia). apply rw_c8_bytesF. exact HN.
    + replace (fs_hint FS 0) with FS by (unfold fs_hint; simpl; lia). exact MU.
Qed.


(* The plain footprint form, by the bridge of asan_stack_malloc_cF_on.v (shadow_rw gives the region). *)
Theorem asan_stack_malloc_0_holds_F : asan_stack_malloc_0_contract_F.
Proof.
  exact (asan_stack_malloc_contract_F_of_F_on 0 ASAN_STACK_MALLOC_0 ASAN_STACK_MALLOC_K asan_stack_malloc_0_holds_F_on).
Qed.
