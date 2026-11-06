(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 503 of its 563 lines of code are new or changed and 644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpSeam.v, with its module paths and module names changed; 837 of its 913 lines of code are new or changed and 487 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpSeamReady.v, with its module paths and module names changed; 215 of its 368 lines of code are new or changed and 760 lines of the source are left out. *)
(* Image B twin of lib/A/RT_pf_chain_sat.v at 915f98b09fb: module paths lib.A -> lib.B, AB1v -> YB1v; 27 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* NON-VACUITY WITNESS for RT_pf_chain.v snprintf_chain_closed.

   snprintf_chain_closed proves PS.snprintf_icpt_stmt GM.set_ready (PS.vf_ready_icpt fr_vfb).  Its premise icpt_ready
   (RT_pf_stmt.v:93-97) asks vf_ready_icpt fr_vfb (RT_pf_stmt.v:193-200), and fr_vfb is GXA's vf_ready_a
   (G_vfprintf_snf.v:218-220) at out_ready := snf_out_ready GM.copy_ready, set_ready := GM.set_ready and
   strn_ready := GC.strn_ready (fr_vfb_unfold).  vf_ready_a asks GXA's pc_guard (G_printf_core_common.v:149-158) at
   every store its footprint reaches (G_vfprintf_snf.v:186-191; fr_vfb_pc_guard).  At the set_ready that asked
   sp < 2 ^ 63 at every n, pc_guard is false at every store and geometry (a Theorem Labs lane's pc_guard_set_false, recorded in
   the header of a Theorem Labs lane's FMgxaSeamReady.v): its memset clause admits sp = Dst >= 2 ^ 63 with a negative N.  Then the
   chain's premise never holds and the theorem says nothing.  RT_gxa_calls_mem.v's set_ready now asks its facts only
   when 0 <= n.

   chain_pc_guard_sat: the premise is satisfiable at the ported set_ready.  At a concrete store sat_m and the geometry
   of reply's snprintf call chain, pc_guard holds at fr_vfb's predicates at every store that the guard's footprint
   reaches from sat_m.  chain_pc_guard_bites: each clause has a call to cover (the memset call has N = 64, so its
   clause does not hold only through set_ready's premise 0 <= n).

   The construction is a Theorem Labs lane's FMgxaSeamSat.v (relocated to reply on a working branch 6e47a021e3f, where it
   does not build: its FMgxaSeamReady.v needs the world field w_H8).  This file takes Sat's store and cells and the
   generic cell lemmas of FMgxaSeamReady.v section 5 that Sat uses (bz_mrd_mbyte .. cells_cons8, proofs unchanged,
   FMupoison.wz copied as wz).  None of them reads w_H8 or any world.  The clauses are proved directly in place of
   Sat's seam_calls_ready (FMgxaSeamGuard.v); the sink's nested munch is as in FMgxaSeamGuard.v vf_ready_a_holds.

   The geometry, with S the snprintf caller's sp at __wrap_snprintf (RT_pf_stmt.v snprintf_icpt_stmt):
     S  = 0x7fffffffe000        page-aligned, 8 KiB below 2 ^ 47
     qv = S - 96 - 2160         musl vsnprintf's sp (PF_SNF_FRAME + PF_VSN_FRAME, icpt_ready's qv)
     q  = qv - 304 - 48         musl vfprintf's sp = S - 0xa30: GXA's vsnprintf_ready gives vf_ready the sp qv - 304
                                (VfprintfCall.v:50), and vf_ready_icpt gives fr_vfb that sp minus PF_VF_FRAME
     Fp = qv - 304 = q + 48     musl vsnprintf's FILE (VfprintfCall.v:50)
     CK = qv - 72 = Fp + 232    its cookie
     lo = q - 5600              vf_ready_icpt's window lo <= (q + 48) - VFI_DEPTH, with equality
     D  = S + 64, dn = 32       the destination: 32 bytes in the snprintf caller's frame, above S
   The store holds every ASan shadow byte as 0, the runtime cells the three ready predicates read, and the bytes of
   [lo, CK + 16) and of the destination.  A store that a munch over the footprint reaches keeps the shadow and every
   byte below the footprint, so each clause closes through the predicates' own introduction lemmas
   (GM.copy_ready_intro, GM.set_ready_intro, GC.strn_ready_intro). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP09 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YO0f.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_snfsink.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.StrnlenCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Common.PropExec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.Shadow.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memcpyw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memsetw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memchrw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls_mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_chain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module YO := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YO0f.
Module CJM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module RSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module GXI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.
Module GCA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_snfsink.
Module GV := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GAF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Module GCC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.StrnlenCall.
Module BzPE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Common.PropExec.
Module BzI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Module BzM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Module BzCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Module BSh := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.Shadow.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Module BMW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memcpyw.
Module BSW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memsetw.
Module BCW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memchrw.
Module BNW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Module GM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls_mem.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Module PC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_chain.

#[local] Existing Instance A_img.

(* ===================================================================================== *)
(* 1. the premise the chain carries                                                       *)
(* ===================================================================================== *)

(* fr_vfb, read off the type of GXA's closed guarded vfprintf body, is vf_ready_a at reply's three predicates *)
Lemma fr_vfb_unfold : forall INV : (word -> option byte) -> Prop,
  PC.fr_vfb INV = GV.vf_ready_a (GS.snf_out_ready GM.copy_ready) GM.set_ready GC.strn_ready GM.copy_ready INV.
Proof. intros INV. reflexivity. Qed.

(* and it carries pc_guard at GM.set_ready, at every store its footprint reaches (G_vfprintf_snf.v:188-190) *)
Lemma fr_vfb_pc_guard : forall INV m q lo Fp CK D dn N bufp A VA fmt slots args,
  PC.fr_vfb INV m q lo Fp CK D dn N bufp A VA fmt slots args ->
  forall m1, CJF.munch (GV.vf_snf_fp lo q Fp CK D dn) m m1 -> CJF.wmono RSt.img_segs m m1 ->
  GCA.pc_guard (GS.snf_out_ready GM.copy_ready Fp (q - 352) CK D dn) GM.set_ready GC.strn_ready INV
    m1 lo (q - 368) (GV.vf_snf_fp lo q Fp CK D dn).
Proof.
intros INV m q lo Fp CK D dn N bufp A VA fmt slots args H m1 MU WM.
rewrite fr_vfb_unfold in H. unfold GV.vf_ready_a, GV.vf_snf_guard in H. destruct H as [_ G].
exact (proj1 (proj2 (proj2 (proj2 (G m1 MU WM))))).
Qed.

(* ===================================================================================== *)
(* 2. the geometry                                                                        *)
(* ===================================================================================== *)

Definition SAT_S : Z := 0x7fffffffe000.          (* the snprintf caller's sp *)
Definition SAT_q : Z := SAT_S - 0xa30.           (* musl vfprintf's sp *)
Definition SAT_lo : Z := SAT_q - 5600.           (* (q + PF_VF_FRAME) - VFI_DEPTH *)
Definition SAT_Fp : Z := SAT_q + 0x30.           (* musl vsnprintf's FILE *)
Definition SAT_CK : Z := SAT_Fp + 0xe8.          (* its cookie *)
Definition SAT_D : Z := SAT_S + 0x40.            (* the destination, in the snprintf caller's frame *)
Definition SAT_dn : nat := 32.

(* the runtime cells all lie below this bound, far below the footprint *)
Definition CELL_TOP : Z := 0x140000.

Lemma sat_eqs :
  SAT_q = 0x7fffffffd5d0 /\ SAT_lo = 0x7fffffffbff0 /\ SAT_Fp = 0x7fffffffd600 /\ SAT_CK = 0x7fffffffd6e8 /\
  SAT_D = 0x7fffffffe040 /\ Z.of_nat SAT_dn = 32 /\ CELL_TOP = 0x140000 /\
  GCA.OUT_DEPTH = 4640 /\ GSC.SET_DEPTH = 2224 /\ GNC.STRN_DEPTH = 4384 /\ GCC.COPY_DEPTH = 2240 /\
  GCC.SN_WRITE_DEPTH = 2304 /\ GXI.SNF_CAP = 80 /\ BR.kHighShadowEnd = 0x10007fff7fff /\
  GAF.HIGHMEM_BEG = 0x10007fff8000 /\ GAF.APPMEM_END = 0x800000000000.
Proof. repeat split. all: reflexivity. Qed.

Local Ltac geo := generalize sat_eqs; lia.

(* ===================================================================================== *)
(* 3. the store                                                                           *)
(* ===================================================================================== *)

(* ASan's shadow, as AsanFacts.in_shadow (AsanFacts.v:17-18) *)
Definition sat_shadow_b (a : Z) : bool :=
  (GAF.LOWMEM_END <=? a) && (a <? GAF.LOWSHADOW_END) || (GAF.HIGHSHADOW_BEG <=? a) && (a <? GAF.HIGHMEM_BEG).

(* the runtime cells (address, width, value), each the cell of one of the six cell predicates:
   R_m2s.m2s_cells, I_memcpyw.icells, I_memsetw.icells_ms, I_strnlenw.icells_sn / icells_sns, I_memchrw.icells_mc *)
Definition sat_cells : list (Z * nat * Z) :=
  [(0x9df40, 8%nat, 0x138168);        (* GOT: common_flags_dont_use *)
   (0x9df50, 8%nat, 0xa6638);         (* GOT: __asan_shadow_memory_dynamic_address *)
   (0x9df58, 8%nat, 0xa7328);         (* GOT: kMidMemBeg *)
   (0x9df60, 8%nat, 0xa7330);         (* GOT: kMidMemEnd *)
   (0x9df68, 8%nat, 0xa7320);         (* GOT: kHighMemEnd *)
   (0x9eab8, 8%nat, 0xa7319);         (* GOT: the flag byte *)
   (0x9fca8, 8%nat, 0x96950);         (* REAL(memchr) = musl memchr *)
   (0x9fd98, 8%nat, 0x973c8);         (* REAL(strnlen) = musl strnlen *)
   (0x9fde8, 8%nat, 0x96a4c);         (* REAL(memcpy) = musl memcpy *)
   (0x9fdf0, 8%nat, 0x96e80);         (* REAL(memset) = musl memset *)
   (0xa6638, 8%nat, 0x7fff8000);      (* the shadow offset *)
   (0xa7318, 1%nat, 1);               (* asan_inited *)
   (0xa7319, 1%nat, 1);               (* the flag byte *)
   (0xa7320, 8%nat, 0x7fffffffffff);  (* kHighMemEnd *)
   (0xa7328, 8%nat, 0);               (* kMidMemBeg *)
   (0xa7330, 8%nat, 0);               (* kMidMemEnd *)
   (0x138263, 1%nat, 1)].             (* common_flags_dont_use + 251 *)

Fixpoint cell_byte (cs : list (Z * nat * Z)) (a : Z) : option Z :=
  match cs with
  | [] => None
  | (b, w, v) :: cs' =>
      if (b <=? a) && (a <? b + Z.of_nat w) then Some (YO.le_byte v w (Z.to_nat (a - b))) else cell_byte cs' a
  end.

(* the application bytes the clauses name: the stack window, the FILE and the cookie (one interval, [lo, CK + 16)),
   and the destination *)
Definition sat_app_b (a : Z) : bool :=
  (SAT_lo <=? a) && (a <? SAT_CK + 16) || (SAT_D <=? a) && (a <? SAT_D + Z.of_nat SAT_dn).

Definition sat_byte (a : Z) : option byte :=
  if sat_shadow_b a then Some (Z_to_bv 8 0)
  else match cell_byte sat_cells a with
       | Some z => Some (Z_to_bv 8 z)
       | None => if sat_app_b a then Some (Z_to_bv 8 0) else None
       end.

Definition sat_m (x : word) : option byte := sat_byte (bv_unsigned x).

Lemma wz : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

(* ---- the shadow: present and 0 ---- *)
Lemma sat_m_shadow : forall s, GAF.in_shadow s -> sat_m (CJM.wa s) = Some (Z_to_bv 8 0).
Proof.
intros s Hs. pose proof (GAF.in_shadow_range s Hs) as [R0 R1].
unfold sat_m. rewrite CJM.wa_unsigned by lia. unfold sat_byte.
replace (sat_shadow_b s) with true; [reflexivity|].
symmetry. unfold sat_shadow_b. unfold GAF.in_shadow in Hs.
destruct Hs as [Hs|Hs]; apply orb_true_iff; [left|right]; apply andb_true_iff;
  (split; [apply Z.leb_le | apply Z.ltb_lt]); lia.
Qed.

Lemma sat_shadow_rw : GAF.shadow_rw sat_m.
Proof.
intros a Ha. unfold wview, CJM.mrd. rewrite (sat_m_shadow a Ha).
split; [discriminate | eexists; reflexivity].
Qed.

Lemma sat_addr_byte : forall a, GAF.app_mem a -> GAF.addr_byte sat_m a.
Proof.
intros a Ha. split; [exact Ha|]. exists (Z_to_bv 8 0). split.
- unfold CJM.mrd. rewrite (sat_m_shadow _ (GAF.shadow_of_app a Ha)). reflexivity.
- unfold GAF.shadow_ok. left. reflexivity.
Qed.

(* every high range that ends 7 bytes below 2^47 is addressable for GXA *)
Lemma sat_pf_rng : forall p n,
  GAF.HIGHMEM_BEG <= p -> 0 <= n <= 2 ^ 40 -> p + n + 7 <= GAF.APPMEM_END -> GAF.pf_rng sat_m p n.
Proof.
intros p n H1 H2 H3.
split; [lia|]. split; [|split].
- split; [unfold GAF.HIGHMEM_BEG in H1; lia|]. split; [lia|]. split; [lia|].
  intros i Hi. apply sat_addr_byte. unfold GAF.app_mem. lia.
- unfold GAF.end_in_app. right. unfold GAF.app_mem. lia.
- intros i Hi. unfold GAF.app_mem. lia.
Qed.

(* ---- the runtime's fixed cells as the interceptors read them: FMgxaSeamReady.v section 5, bz_mrd_mbyte ..
   cells_cons8, proofs unchanged ---- *)
Lemma bz_mrd_mbyte : forall (m : word -> option byte) a, BzM.mrd BzI.asegs m (BzM.wa a) = mbyte tfibsegs m a.
Proof. intros m a. reflexivity. Qed.

Lemma le_byte1 : forall v, 0 <= v < 256 -> Z_to_bv 8 (YO.le_byte v 1 0) = Z_to_bv 8 v.
Proof.
intros v Hv. unfold YO.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia.
reflexivity.
Qed.

Lemma nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma le8_nth : forall v k, 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  nth_error (BzM.le8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (YO.le_byte v 8 k)).
Proof.
intros v k Hv Hk. unfold BzM.le8, word_to_le_bytes. rewrite nth_le_bytes by exact Hk.
rewrite (wz v Hv). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO.le_byte, bv_wrap.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia.
change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma c8_of_val_mem : forall (m : word -> option byte) a v,
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m a 8 v ->
  BzSt.ro_cells BzI.asegs m a [BzCl.C8 (Z_to_bv 64 v)].
Proof.
intros m a v Ha Ha8 Hv HV. unfold BzSt.ro_cells, BzCl.cells_at. split; [cbn; tauto|].
cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r.
split; [exact Ha|]. split; [rewrite BzM.length_le8; cbn; lia|].
intros i Hi. rewrite BzM.length_le8 in Hi. rewrite (le8_nth v i Hv Hi), bz_mrd_mbyte. exact (HV i Hi).
Qed.

Lemma c1_of_val_mem : forall (m : word -> option byte) a v,
  0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= v < 256 -> val_mem tfibsegs m a 1 v ->
  BzSt.ro_cells BzI.asegs m a [BzCl.C1 (Z_to_bv 8 v)].
Proof.
intros m a v Ha Ha1 Hv HV. unfold BzSt.ro_cells, BzCl.cells_at. split; [cbn; tauto|].
cbn [BzCl.cells_bytes BzCl.cbytes app].
split; [exact Ha|]. split; [cbn; lia|].
intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
rewrite bz_mrd_mbyte. cbn [nth_error]. rewrite (HV 0%nat ltac:(lia)), (le_byte1 v Hv). reflexivity.
Qed.

Lemma wview_of_mrd : forall (m : word -> option byte) (x : word) b,
  BzM.mrd BzI.asegs m x = Some b -> BzM.ro_addr BzI.asegs x = false -> wview BzI.asegs m x <> None.
Proof.
intros m x b H R. unfold wview. destruct (m x) as [c|] eqn:E; [discriminate|].
unfold BzM.mrd in H. rewrite E in H. unfold BzM.ro_addr in R. unfold BzPE.seg_rom, memory_read in H.
change (Z.of_N 1) with 1 in H.
destruct (find_segment BzI.asegs (bv_unsigned x) 1) as [s|]; [|discriminate H].
apply negb_false_iff in R. rewrite R.
destruct (seg_readable s); [|discriminate H].
destruct (segment_byte_at (seg_bytes s) (Z.to_N (bv_unsigned x - Z.of_N (seg_base s)))) eqn:Eb; [discriminate|].
exfalso. simpl in H. rewrite Eb in H. discriminate H.
Qed.

Definition rw_range (a : Z) (n : nat) : bool :=
  forallb (fun i => negb (BzM.ro_addr BzI.asegs (BzM.wa (a + Z.of_nat i)))) (seq 0 n).

Lemma rw_of_ro : forall (m : word -> option byte) a cs,
  BzSt.ro_cells BzI.asegs m a cs -> rw_range a (BzCl.cells_size cs) = true -> BzSt.rw_cells BzI.asegs m a cs.
Proof.
intros m a cs HC HRO. split; [exact HC|]. destruct HC as (Hwf & Hb).
pose proof (BzM.bytes_at_bound BzI.asegs m a _ Hb) as (H0 & H1). rewrite (BzCl.cells_bytes_length cs Hwf) in H1.
split; [exact H0|]. split; [exact H1|]. intros i Hi.
destruct Hb as (_ & _ & Hb).
specialize (Hb (Z.to_nat i) ltac:(rewrite (BzCl.cells_bytes_length cs Hwf); lia)).
rewrite Z2Nat.id in Hb by lia.
destruct (nth_error (BzCl.cells_bytes cs) (Z.to_nat i)) as [b|] eqn:E;
  [| apply nth_error_None in E; rewrite (BzCl.cells_bytes_length cs Hwf) in E; lia].
apply (wview_of_mrd m _ b Hb).
unfold rw_range in HRO. pose proof (proj1 (forallb_forall _ _) HRO (Z.to_nat i)) as Hi'.
rewrite in_seq in Hi'. specialize (Hi' ltac:(lia)). rewrite Z2Nat.id in Hi' by lia.
apply negb_true_iff in Hi'. exact Hi'.
Qed.

Lemma cells_cons : forall (m : word -> option byte) a c cs,
  BzSt.ro_cells BzI.asegs m a [c] -> BzSt.ro_cells BzI.asegs m (a + Z.of_nat (BzCl.csize c)) cs ->
  BzSt.ro_cells BzI.asegs m a (c :: cs).
Proof.
intros m a c cs (W1 & B1) (W2 & B2). destruct W1 as (Wc & _).
split; [split; [exact Wc | exact W2]|].
cbn [BzCl.cells_bytes] in B1 |- *. rewrite app_nil_r in B1.
apply (proj2 (BzM.bytes_at_app BzI.asegs m a _ _)). split; [exact B1|].
rewrite (BzCl.cbytes_length c Wc). exact B2.
Qed.

Lemma cells_cons8 : forall (m : word -> option byte) a w cs,
  BzSt.ro_cells BzI.asegs m a [BzCl.C8 w] -> BzSt.ro_cells BzI.asegs m (a + 8) cs ->
  BzSt.ro_cells BzI.asegs m a (BzCl.C8 w :: cs).
Proof. intros m a w cs H1 H2. apply cells_cons; [exact H1 | exact H2]. Qed.

(* ---- the runtime cells, at every store that agrees with sat_m below CELL_TOP ---- *)
Definition cell_ok_b (a : Z) (w : nat) (v : Z) : bool :=
  forallb (fun k => negb (sat_shadow_b (a + Z.of_nat k)) &&
                    match cell_byte sat_cells (a + Z.of_nat k) with
                    | Some z => Z.eqb z (YO.le_byte v w k)
                    | None => false
                    end) (seq 0 w).

Lemma sat_val_mem : forall (m' : word -> option byte) a w v,
  (forall x : word, bv_unsigned x < CELL_TOP -> m' x = sat_m x) ->
  0 <= a -> a + Z.of_nat w <= CELL_TOP -> cell_ok_b a w v = true ->
  val_mem tfibsegs m' a w v.
Proof.
intros m' a w v AG Ha Haw OK k Hk.
unfold cell_ok_b in OK. rewrite forallb_forall in OK.
specialize (OK k ltac:(apply in_seq; lia)). cbv beta in OK.
apply andb_true_iff in OK as [E1 E2]. apply negb_true_iff in E1.
destruct (cell_byte sat_cells (a + Z.of_nat k)) as [z|] eqn:E3; [|discriminate E2].
apply Z.eqb_eq in E2.
unfold CELL_TOP in AG, Haw. unfold mbyte.
rewrite AG by (rewrite wz by lia; lia).
unfold sat_m. rewrite wz by lia. unfold sat_byte. rewrite E1, E3, E2. reflexivity.
Qed.

Local Ltac c8 AG := eapply c8_of_val_mem;
  [lia | lia | lia | apply (sat_val_mem _ _ _ _ AG); [lia | unfold CELL_TOP; lia | vm_compute; reflexivity]].
Local Ltac c1 AG := eapply c1_of_val_mem;
  [lia | lia | lia | apply (sat_val_mem _ _ _ _ AG); [lia | unfold CELL_TOP; lia | vm_compute; reflexivity]].

(* the six cell predicates the three ready predicates carry *)
Lemma sat_cells_at : forall m' : word -> option byte,
  (forall x : word, bv_unsigned x < CELL_TOP -> m' x = sat_m x) ->
  BR.m2s_cells m' /\ BMW.icells m' /\ BSW.icells_ms m' /\ BNW.icells_sn m' /\ BCW.icells_mc m' /\ BNW.icells_sns m'.
Proof.
intros m' AG.
split; [|split; [|split; [|split; [|split]]]].
- unfold BR.m2s_cells, BSh.SHB, BR.kHighMemEnd.
  split; [|split]; (apply rw_of_ro; [|vm_compute; reflexivity]).
  + apply cells_cons8; [c8 AG|]. apply cells_cons8; [c8 AG|]. apply cells_cons8; [c8 AG|]. c8 AG.
  + c8 AG.
  + apply cells_cons8; [c8 AG|]. apply cells_cons8; [c8 AG|]. c8 AG.
- unfold BMW.icells. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG | c1 AG].
- unfold BSW.icells_ms. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG | c1 AG].
- unfold BNW.icells_sn. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG|].
  split; [apply rw_of_ro; [c1 AG | vm_compute; reflexivity] | c1 AG].
- unfold BCW.icells_mc. split; [c8 AG|]. split; [c8 AG|].
  split; [c8 AG | apply rw_of_ro; [c1 AG | vm_compute; reflexivity]].
- unfold BNW.icells_sns. c8 AG.
Qed.

(* a munch over the footprint keeps every byte below CELL_TOP *)
Lemma sat_agree : forall m' : word -> option byte,
  CJF.munch (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn) sat_m m' ->
  forall x : word, bv_unsigned x < CELL_TOP -> m' x = sat_m x.
Proof.
intros m' MU x Hx. apply MU. unfold GV.vf_snf_fp. cbn [CJF.outside].
split; [geo|]. split; [geo|]. split; [geo|]. split; [geo | exact I].
Qed.

(* the footprint is high application memory, so a munch over it keeps the shadow *)
Lemma sat_all_app : GAF.all_app (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn).
Proof.
unfold GV.vf_snf_fp. cbn [GAF.all_app].
split; [|split; [|split; [|split; [|exact I]]]]; apply GAF.high_stack_app; geo.
Qed.

(* ===================================================================================== *)
(* 4. the witness                                                                         *)
(* ===================================================================================== *)

(* pc_guard at fr_vfb's predicates (fr_vfb_pc_guard's conclusion, with INV holding everywhere: the evt -> SRr bridge
   chooses INV), at every store the guard's footprint reaches from sat_m *)
Theorem chain_pc_guard_sat : forall m1 : word -> option byte,
  CJF.munch (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn) sat_m m1 -> CJF.wmono RSt.img_segs sat_m m1 ->
  GCA.pc_guard (GS.snf_out_ready GM.copy_ready SAT_Fp (SAT_q - 352) SAT_CK SAT_D SAT_dn) GM.set_ready GC.strn_ready
    (fun _ => True) m1 SAT_lo (SAT_q - 368) (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn).
Proof.
intros m1 MU1 WM1. unfold GCA.pc_guard. intros m2 MU2 WM2.
assert (MU02 : CJF.munch (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn) sat_m m2)
  by (eapply CJF.munch_trans; [exact MU1 | exact MU2]).
assert (WM02 : CJF.wmono RSt.img_segs sat_m m2) by (eapply CJF.wmono_trans; [exact WM1 | exact WM2]).
pose proof (GAF.munch_meta _ _ _ MU02 sat_all_app) as MK2.
pose proof (GAF.munch_meta _ _ _ MU2 sat_all_app) as MK12.
pose proof (sat_cells_at m2 (sat_agree m2 MU02)) as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (GAF.shadow_rw_kept sat_m m2 sat_shadow_rw MK2 WM02) as SRW2.
split; [exact I|]. split; [|split].
- (* memcpy through the snprintf sink, with the sink's frame at sp - 64 *)
  intros sp S L HS1 HS2 HSRC. unfold GS.snf_out_ready.
  intros m3 Dst P N MU3 WM3 HDST HN HP.
  assert (MU23 : CJF.munch (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn) m2 m3).
  { eapply CJF.munch_weaken; [|exact MU3].
    unfold CJF.sub_fp, GCC.sn_write_footprint, GV.vf_snf_fp. cbn [CJF.outside]. intros x Hx. geo. }
  assert (MU03 : CJF.munch (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn) sat_m m3)
    by (eapply CJF.munch_trans; [exact MU02 | exact MU23]).
  assert (MU13 : CJF.munch (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn) m1 m3)
    by (eapply CJF.munch_trans; [exact MU2 | exact MU23]).
  assert (WM03 : CJF.wmono RSt.img_segs sat_m m3) by (eapply CJF.wmono_trans; [exact WM02 | exact WM3]).
  pose proof (GAF.munch_meta _ _ _ MU03 sat_all_app) as MK3.
  pose proof (GAF.munch_meta _ _ _ MU13 sat_all_app) as MK13.
  pose proof (sat_cells_at m3 (sat_agree m3 MU03)) as (D1 & D2 & _ & _ & _ & _).
  pose proof (GAF.shadow_rw_kept sat_m m3 sat_shadow_rw MK3 WM03) as SRW3.
  assert (PD : GAF.pf_rng m3 Dst N).
  { apply (GAF.pf_rng_kept sat_m m3 Dst N); [|exact MK3].
    destruct HDST as [[HD1 HD2]|[HD1 HD2]]; apply sat_pf_rng; geo. }
  assert (PS : GAF.pf_rng m3 P N).
  { destruct HP as [[-> HP]|[-> HP]].
    - apply (GAF.pf_rng_kept sat_m m3 _ N); [apply sat_pf_rng; geo | exact MK3].
    - destruct HSRC as [[HS3 HS4]|HSRC].
      + apply (GAF.pf_rng_kept sat_m m3 S N); [apply sat_pf_rng; geo | exact MK3].
      + apply (GAF.pf_rng_kept m1 m3 S N); [|exact MK13].
        apply (GCF.pf_rng_prefix m1 S L N HSRC). lia. }
  apply (GM.copy_ready_intro m3 (sp - 64) Dst P N N N); [geo | geo | exact HN | | exact PD | exact PS | exact SRW3
                                                        | lia | lia | exact D1 | exact D2].
  right; right. destruct HDST as [[HD1 HD2]|[HD1 HD2]]; geo.
- (* memset *)
  intros sp Dst N H1 H2 H3.
  destruct (Z_le_gt_dec 0 N) as [HN|HN]; [|intros HN'; lia].
  apply (GM.set_ready_intro m2 sp Dst N N); [geo | geo | exact HN | right; right; exact H2 | | exact SRW2 | lia
                                            | exact C1 | exact C3].
  apply (GAF.pf_rng_kept sat_m m2 Dst N); [apply sat_pf_rng; geo | exact MK2].
- (* strnlen *)
  intros sp S0 N L buf H1 H2 PR HL.
  apply (GC.strn_ready_intro m2 sp S0 N L buf); [geo | geo | exact (GAF.pf_rng_kept m1 m2 S0 L PR MK12)
                                                | exact SRW2 | exact HL | exact C1 | exact C4 | exact C5 | exact C6].
Qed.

(* each clause bites: at sat_m the three predicates hold at a call each clause covers, with a non-empty range *)
Corollary chain_pc_guard_bites :
  GM.copy_ready sat_m (SAT_q - 368 - 64) SAT_D (SAT_q - 352) 32 /\
  GM.set_ready sat_m (SAT_lo + GSC.SET_DEPTH) (SAT_lo + GSC.SET_DEPTH) 64 /\
  GC.strn_ready sat_m (SAT_q - 368) SAT_D 32 [].
Proof.
destruct (chain_pc_guard_sat sat_m (CJF.munch_refl _ _) (fun x H => H) sat_m (CJF.munch_refl _ _) (fun x H => H))
  as (_ & RC & RS & RT).
split; [|split].
- pose proof (RC (SAT_q - 368) SAT_D 32 ltac:(geo) ltac:(geo)
                (or_intror (sat_pf_rng SAT_D 32 ltac:(geo) ltac:(geo) ltac:(geo)))) as RC1.
  unfold GS.snf_out_ready in RC1.
  apply (RC1 sat_m SAT_D (SAT_q - 352) 32 (CJF.munch_refl _ _) (fun x H => H)); [left; geo | lia | left; geo].
- apply (RS (SAT_lo + GSC.SET_DEPTH) (SAT_lo + GSC.SET_DEPTH) 64); geo.
- apply (RT (SAT_q - 368) SAT_D 32 32 []); [geo | geo | apply sat_pf_rng; geo | apply Z.leb_le; reflexivity].
Qed.
