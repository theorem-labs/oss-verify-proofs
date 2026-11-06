(* Modified by Theorem Labs, 2026-10: moved from image A (fuzz_preset.asan d83eb25d), commit 3244f5c71f6, to the #102 pin A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b): 29 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-A-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan (image A, d83eb25d) from commit 3e35620c52e proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxa_mem.v: module paths (lib/A/FMgxa_mem.v -> lib/A/PSnpL3/FMgxa_mem.v; lib/A/{Spec,Strw,Ox} -> preset's own lib/... (byte-identical modulo module paths, reused); lib/A/RT_IImgA (A_img / A_img_vsn) -> lib/CJ/RL/I/IImgA (N_img_asan / N_img_vsn)) and the address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97), each by symbol + offset in both images (per-numeral report: the relocation record, A-run). *)
(* GXA's interceptor call contracts for memcpy and memset (lib/CJ/RL/GXA/CopyCall.v:29-41 memcpy_stack_contract,
   SetCall.v:28-37 memset_stack_contract), discharged at the ASan instance A_img (RT_IImgA.v:102) on the pinned
   fuzz_manifest.asan, and memset also at A_img_vsn (RT_IImgA.v:113), which RT_gxa_inst.v:108 consumes.  The twin of
   RT_gxa_strnlen.v (strnlen); names, predicates and file shape follow the fuzz_reply port's pf-calls work
   86b50358d34 proofs/plugin-hostd/fuzz_reply/lib/A/RT_gxa_calls_mem.v.
   The two contract proofs are adapted from the same composition, already Qed at fuzz_manifest.asan under other image
   instances, on commit 486fc9eb410 proofs/omx-clap-core/fuzz_manifest/lib:
     memcpy_stack_contract_A  adapted from  lib/A/Prog/vfprintf_snf_closed.v:180-236 memcpy_bridge_R
                                             (@CopyCall.memcpy_stack_contract VSF.N_img_vf copy_okR)
     memset_stack_contract_A  adapted from  lib/A/Prog/vsnprintf_F.v:53-103 memset_bridge_P
                                             (@SetCall.memset_stack_contract InstAsanA.N_img_asan set_okP)
   Adapted to A_img, to copy_ready / set_ready (their guards copy_okR / set_okP less 0 <= D, 0 <= S, 0 <= N and the
   Bz mem_inv, which the contracts supply), and to FMgxa_bzcj.v's bridge in place of CJBridge.v's evt_to_cj /
   mem_inv_to_cj and BzCallBridge.v's rw_cb_to_bz / rw_cb_of_bz.  Those two files are not Required (their Require
   closures bring AsanRT.v and the restricted-memory kit, outside this file's closure).

   This file proves no new function.  It composes walks that are already in the tree, at fuzz_manifest.asan's own
   addresses (the ASan runtime proofs' Bz tree, commit affce6489c8; nothing is relocated):
   - memcpy: the Bz walk of the memcpy interceptor 0x52db0 (lib/A/Bz/A/I_memcpy.v imemcpy_spec, over I_memcpyw.v /
     I_memcpyw2.v), with its two Section hypotheses rip_stmt (R_isPoisoned.v rip_proof) and memcpy_stmt (musl
     memcpy 0x9b2b4: RT_mem_bz.v mc_proof, from the libc walks lib/A/Prog/memcpy.v and memcpy_same.v).
     I_amemcpy.v (amemcpy_spec, the walk entered at 0x523e4) is in the tree only because it states memcpy_stmt; it is
     not used for this contract.
   - memset: the Bz walk of the memset interceptor 0x52ac0 (lib/A/Bz/A/I_imemset.v imemset_spec, over I_memsetw.v),
     with rip_stmt and memset_callZ_stmt (musl memset 0x9b6b8: RT_mem_bz.v ms_callZ_proof, from lib/A/Prog/memset.v).
   - the trampolines: lib/A/Bz/A/I_tramp.v tramp_memcpy (__wrap_memcpy 0x523e0, one `j` to 0x52db0) and
     tramp_memset (__wrap_memset 0x523dc, one `j` to 0x52ac0).
   - the CJ / Bz vocabulary bridge lib/A/FMgxa_bzcj.v (bz_cj_evt, mem_inv_cj_bz, mem_inv_bz_cj, chk_ok_of_pf_rng).
   What it adds is glue only: GXA's call targets under A_img (`sym 0x21334` = 0x523e0, `sym 0x21738` = 0x523dc,
   RT_IImgA.v:67-68; A_img_vsn has the same 0x21738 row), the CB-cell conversion between the two trees (an Inductive
   in each; stk, bytes_at, munch and wmono are the same terms in both and cross by `exact`), and the two ready
   predicates.
   The ready predicates are exactly what the interceptor walks ask beyond the contracts' own premises, with the
   walk's stack floor lo := sp - DEPTH.  GXA's depths equal the walks', with no slack: the memcpy interceptor's
   frame is 2160 bytes (I_memcpy.v: its callees run at sp - 2160) and region_is_poisoned below it takes 80
   (I_consts.v rip_stmt), 2240 = COPY_DEPTH; the memset interceptor's frame is 64 + 2080 = 2144 (I_imemset.v
   carve_frame) plus 80, 2224 = SET_DEPTH.
   - copy_ready m sp d s n: the stack window lies above ASan's high shadow and below 2^63; both ranges end at or
     below 2^47; the destination is off the walk's stack window (the source is already, by the contract); both
     ranges pass the interceptor's range check (chk_ok); ASan's mem-to-shadow cells (m2s_cells) and the cells the
     memcpy interceptor reads (icells: the GOT words 0xa2010 / 0xa2b78 of the shadow cell and of the flag byte
     0xabb99, the flag byte = 1, the shadow offset 0x7fff8000, and REAL(memcpy) = musl memcpy 0x9b2b4 at 0xa3e88).
   - set_ready m sp d n: when 0 <= n, the same for the one destination range, with icells_ms (REAL(memset) = musl
     memset 0x9b6b8 at 0xa3e90).  The length premise is there because GXA's pc_guard (G_printf_core_common.v:157)
     asks set_ready at every D + N + 8 <= q with N unbounded below, where sp < 2^63 cannot follow; the contracts
     apply set_ready only to bv_unsigned lengths, which are non-negative.
   copy_ready_intro / set_ready_intro prove them from GXA's own ASan vocabulary (AsanFacts.v pf_rng / shadow_rw),
   the stack placement and ASan's runtime cells, as RT_gxa_strnlen.v's strn_ready_intro does.
   Numerals introduced here, each keyed on its fuzz_manifest.asan symbol + offset:
     0x523e0  __wrap_memcpy + 0  (the A_img row KV 0x21334 0x523e0; I_tramp.v tramp_memcpy's source pc)
     0x523dc  __wrap_memset + 0  (the A_img row KV 0x21738 0x523dc; I_tramp.v tramp_memset's source pc) *)
(* Modified by Theorem Labs, 2026-10: set_ready asked only when 0 <= n (GXA's pc_guard, G_printf_core_common.v:157, bounds sp only through D + N with N unbounded below, so set_ready's sp < 2 ^ 63 made it unsatisfiable); memset_stack_contract_A and set_ready_intro re-proved for it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_tramp I_memcpyw I_memcpyw2 I_amemcpy I_memcpy I_memsetw F_memset I_imemset.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Cells.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.R_isPoisoned.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Cells.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I.IImgA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.FMgxa_bzcj.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.RT_mem_bz.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Exec.
Module BzM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Mem.
Module BzF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Frame.
Module BzCl := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Step.
Module BzRIP := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.R_isPoisoned.
Module CJS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.MState.
Module CJM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Frame.
Module CJCl := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Cells.
Module CJSt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.
Module CJR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RStep.
Module GXC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.CopyCall.
Module GXM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.SetCall.
Module GXF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I.IImgA.
Module BC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.FMgxa_bzcj.
Module RMB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.RT_mem_bz.

(* ---- GXA's call targets: the trampolines (RT_IImgA.v:67-68) ---- *)

(* __wrap_memcpy 0x523e0: `j` to the memcpy interceptor 0x52db0 (I_tramp.v tramp_memcpy) *)
Lemma A_sym_memcpy : @CJR.sym RTA.N_img_asan 0x21334 = 0x523e0.
Proof. vm_compute. reflexivity. Qed.

(* __wrap_memset 0x523dc: `j` to the memset interceptor 0x52ac0 (I_tramp.v tramp_memset) *)
Lemma A_sym_memset : @CJR.sym RTA.N_img_asan 0x21738 = 0x523dc.
Proof. vm_compute. reflexivity. Qed.

(* musl vsnprintf's instance has the same memset row *)
Lemma A_sym_vsn_memset : @CJR.sym RTA.N_img_vsn 0x21738 = 0x523dc.
Proof. vm_compute. reflexivity. Qed.

(* Both instances' segments are fuzz_manifest.asan's loaded segments (RT_IImgA.v:102, :113), the Bz tree's asegs.
   Each is stated against asegs on purpose: `change (img_segs A_img_vsn) with (img_segs A_img)` did not finish in
   300 s (measured), the unifier comparing the two records' sym fields, tsym over two different tables. *)
Lemma A_segs : @CJR.img_segs RTA.N_img_asan = asegs.
Proof. reflexivity. Qed.

Lemma A_vsn_segs : @CJR.img_segs RTA.N_img_vsn = asegs.
Proof. reflexivity. Qed.

(* ---- the CB cell, an Inductive in each tree ---- *)

Lemma rw_cb_cj_bz : forall m a k bs,
  @CJSt.rw_cells (@CJR.img_segs RTA.N_img_asan) m a [CJCl.CB k bs] -> BzSt.rw_cells asegs m a [BzCl.CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

Lemma rw_cb_bz_cj : forall m a k bs,
  BzSt.rw_cells asegs m a [BzCl.CB k bs] -> @CJSt.rw_cells (@CJR.img_segs RTA.N_img_asan) m a [CJCl.CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

(* ---- memcpy ---- *)

Definition copy_ready (m : word -> option byte) (sp d s n : Z) : Prop :=
  kHighShadowEnd < sp - GXC.COPY_DEPTH /\ sp < 2 ^ 63
  /\ d + n <= 2 ^ 47 /\ s + n <= 2 ^ 47
  /\ (n = 0 \/ d + n <= sp - GXC.COPY_DEPTH \/ sp <= d)
  /\ chk_ok m s n /\ chk_ok m d n
  /\ m2s_cells m /\ icells m.

(* adapted from commit 486fc9eb410 lib/A/Prog/vfprintf_snf_closed.v:180-236 memcpy_bridge_R *)
Theorem memcpy_stack_contract_A : @GXC.memcpy_stack_contract RTA.N_img_asan copy_ready.
Proof.
  unfold GXC.memcpy_stack_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m src junk SRC LEN DST OV SSEP MI ST G.
  destruct G as (HS & QT & DN & SN & SEP & CS & CD & M2S & IC).
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R0, R1, R2.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R0, R1, R2.
  assert (EN : Z.of_nat (length src) = bv_unsigned a2) by (rewrite LEN; apply Z2Nat.id; lia).
  rewrite A_sym_memcpy.
  apply BC.bz_cj_evt.
  apply (BzE.evt_mono asegs (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
            (bv_unsigned a0) (bv_unsigned a1) src (bv_unsigned sp - GXC.COPY_DEPTH) m)).
  { rewrite BC.ms_cj_bz, BC.mkR_cj_bz, BC.seg_rom_cj_bz.
    apply tramp_memcpy.
    apply (imemcpy_spec BzRIP.rip_proof RMB.mc_proof
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m (bv_unsigned a0) (bv_unsigned a1) src junk (bv_unsigned sp - GXC.COPY_DEPTH));
      rewrite ?EN.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - exact ST.
    - unfold GXC.COPY_DEPTH. lia.
    - exact HS.
    - exact QT.
    - lia.
    - lia.
    - exact DN.
    - exact SN.
    - lia.
    - unfold GXC.COPY_DEPTH in SSEP. right. exact SSEP.
    - unfold GXC.COPY_DEPTH in SEP. exact SEP.
    - exact SRC.
    - rewrite LEN. exact (rw_cb_cj_bz m _ _ _ DST).
    - exact CS.
    - exact CD.
    - exact M2S.
    - exact IC.
    - exact (BC.mem_inv_cj_bz m MI). }
  intros ms' HQ.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & RW & B).
  rewrite EN in MU. rewrite LEN in RW.
  unfold GXC.memcpy_stack_post.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [rewrite E, Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact MU|].
  split; [exact WM|].
  split; [exact (BC.mem_inv_bz_cj m' MI')|].
  split; [exact ST'|].
  split; [exact (rw_cb_bz_cj m' _ _ _ RW) | exact B].
Qed.

(* copy_ready from what GXA's caller holds at a memcpy call (sn_write_ready, CopyCall.v:46-51: the stack placement,
   the destination inside the caller's buffer and the source inside a range GXA calls addressable), a readable
   shadow and ASan's runtime cells. *)
Lemma copy_ready_intro : forall (m : word -> option byte) sp d s n Ld Ls,
  kHighShadowEnd < sp - GXC.COPY_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXC.COPY_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTA.N_img_asan m d Ld -> @GXF.pf_rng RTA.N_img_asan m s Ls -> @GXF.shadow_rw RTA.N_img_asan m ->
  n <= Ld -> n <= Ls ->
  m2s_cells m -> icells m ->
  copy_ready m sp d s n.
Proof.
  intros m sp d s n Ld Ls H1 H2 N0 SEPD PD PS SRW HD HS C1 C2.
  split; [exact H1|]. split; [exact H2|].
  split; [destruct PD as (_ & (_ & _ & Hpn & _) & _); unfold GXF.APPMEM_END in Hpn; lia|].
  split; [destruct PS as (_ & (_ & _ & Hpn & _) & _); unfold GXF.APPMEM_END in Hpn; lia|].
  split; [exact SEPD|].
  split; [exact (BC.chk_ok_of_pf_rng m s Ls n PS SRW HS)|].
  split; [exact (BC.chk_ok_of_pf_rng m d Ld n PD SRW HD)|].
  exact (conj C1 C2).
Qed.

(* ---- memset ---- *)

Definition set_ready (m : word -> option byte) (sp d n : Z) : Prop :=
  0 <= n ->
  kHighShadowEnd < sp - GXM.SET_DEPTH /\ sp < 2 ^ 63
  /\ d + n <= 2 ^ 47
  /\ (n = 0 \/ d + n <= sp - GXM.SET_DEPTH \/ sp <= d)
  /\ chk_ok m d n
  /\ m2s_cells m /\ icells_ms m.

(* adapted from commit 486fc9eb410 lib/A/Prog/vsnprintf_F.v:53-103 memset_bridge_P *)
Theorem memset_stack_contract_A : @GXM.memset_stack_contract RTA.N_img_asan set_ready.
Proof.
  unfold GXM.memset_stack_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m junk DST MI ST G.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as RC.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R0, RC, R2.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R0, RC, R2.
  destruct (G (proj1 R2)) as (HS & QT & DN & SEP & CK & M2S & IC).
  rewrite A_sym_memset.
  apply BC.bz_cj_evt.
  apply (BzE.evt_mono asegs (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
            (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp - GXM.SET_DEPTH) m)).
  { rewrite BC.ms_cj_bz, BC.mkR_cj_bz, BC.seg_rom_cj_bz.
    apply tramp_memset.
    apply (imemset_spec BzRIP.rip_proof RMB.ms_callZ_proof
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) junk
             (bv_unsigned sp - GXM.SET_DEPTH)).
    - symmetry. apply Z_to_bv_bv_unsigned.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - exact ST.
    - unfold GXM.SET_DEPTH. lia.
    - exact HS.
    - exact QT.
    - lia.
    - lia.
    - exact DN.
    - lia.
    - unfold GXM.SET_DEPTH in SEP. exact SEP.
    - exact (rw_cb_cj_bz m _ _ _ DST).
    - exact CK.
    - exact M2S.
    - exact IC.
    - exact (BC.mem_inv_cj_bz m MI). }
  intros ms' HQ.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & RW).
  unfold GXM.memset_stack_post.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [rewrite E, Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact MU|].
  split; [exact WM|].
  split; [exact (BC.mem_inv_bz_cj m' MI')|].
  split; [exact ST'|].
  exact (rw_cb_bz_cj m' _ _ _ RW).
Qed.

(* musl vsnprintf's instance (RT_gxa_inst.v:108).  A_img_vsn differs from A_img only at 0x7f000400 and has the same
   segments (RT_IImgA.v:111-113), so once the call target and the segments are rewritten to A_img's the A_img proof
   is the proof. *)
Theorem memset_stack_contract_Avsn : @GXM.memset_stack_contract RTA.N_img_vsn set_ready.
Proof.
  unfold GXM.memset_stack_contract, GXM.memset_stack_post.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m junk DST MI ST G.
  rewrite A_sym_vsn_memset, <- A_sym_memset.
  rewrite A_vsn_segs in DST, MI, ST |- *. rewrite <- A_segs in DST, MI, ST |- *.
  pose proof (memset_stack_contract_A ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                s10 s11 t3 t4 t5 t6 F fc m junk DST MI ST G) as H.
  unfold GXM.memset_stack_post in H.
  exact H.
Qed.

(* set_ready from what GXA's caller holds at a memset call: the stack placement, the destination inside a range GXA
   calls addressable, a readable shadow and ASan's runtime cells. *)
Lemma set_ready_intro : forall (m : word -> option byte) sp d n Ld,
  kHighShadowEnd < sp - GXM.SET_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXM.SET_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTA.N_img_asan m d Ld -> @GXF.shadow_rw RTA.N_img_asan m -> n <= Ld ->
  m2s_cells m -> icells_ms m ->
  set_ready m sp d n.
Proof.
  intros m sp d n Ld H1 H2 N0 SEPD PD SRW HD C1 C2 _.
  split; [exact H1|]. split; [exact H2|].
  split; [destruct PD as (_ & (_ & _ & Hpn & _) & _); unfold GXF.APPMEM_END in Hpn; lia|].
  split; [exact SEPD|].
  split; [exact (BC.chk_ok_of_pf_rng m d Ld n PD SRW HD)|].
  exact (conj C1 C2).
Qed.
