(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/SecGrantW.v (a working branch 30a1993588f, c5 + memnorm; file sha256 a04e1c05fd13) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* The grant-existence field of the widened secondary interface, AGif4.ifs_grant_w, from a Theorem Labs lane's parametric LPS
   placement lemma SecGrantP.sec_grant_exists_live_P (SecGrantP.v:88-99, :306-315).

   AGif4.ifs_grant_w ARX NOBW asks: for every pre-state of the allocator relation ARX and every size
   0 < sz <= NOBW, a placement witness (grant_ok_na_pin) exists on the model the walk asks the kernel with, i.e.
   on [with_vm_backing (m_vm_lazy md) mat md] for any materialized-page list mat.  SecGrantP gives the witness on
   a model whose ledger covers its maps; the ledger facts it reads (ledger_cover, amwf's non-empty maps) depend on
   [m_vmmaps] and [m_vm_lazy] only, which with_vm_backing keeps, so the witness carries over.

   [ifs_grant_w_P]   the field at any (nob, lim, mmax) satisfying SecGrantP's side conditions, from what each
                     pre-state of ARX gives: layout_ok, the chunk facts, the ledger cover over sec_extents ++ xs,
                     amwf, the live count, and the sizes of the extra extents xs.
   [ifs_grant_w_cf]  the same at a unit's CfParams (YGcfNames.v:114-190): nob := cf_nob, lim := cf_place_limit,
                     mmax := cf_malloc_max, whose fields cf_nob_lo / cf_nob_al / cf_place_ok / cf_sizes_ok are
                     exactly SecGrantP's side conditions.  A unit takes this lemma by path and supplies its
                     instance's per-state facts.

   No unit's numbers appear here: they are the CfParams instance's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0v YK00 YK13 YK06 YK04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG0a YG01 YG0n YG0h YG08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YF06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import SecGrantP YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGif4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg}.

(* SecGrantP's ledger facts only read the model's maps; with_vm_backing keeps them. *)
Lemma ledger_cover_wvb : forall segs ly md zs mat,
ledger_cover segs ly md zs -> ledger_cover segs ly (with_vm_backing (m_vm_lazy md) mat md) zs.
Proof. intros segs ly md zs mat L. unfold ledger_cover in *. rewrite !m_vmmaps_wvb. exact L. Qed.
Lemma amwf_wvb : forall md mat, amwf md -> amwf (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat H. apply (amwf_same md); [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact H]. Qed.

Section P.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variables (nob lim mmax : Z).
Hypothesis HN : 536870912 <= nob.
Hypothesis HNal : nob mod 4096 = 0.
Hypothesis HW : 0x2aaaaaaab000 + (257 * 25 + lim) * (2 * nob) + nob <= 0x7fff7f800000.
Hypothesis HSZ : forall n, 0 <= n < mmax -> sec_map_size n <= nob.
(* the extra mapped extents the instance's ledger covers besides the lazy zones and the live secondaries *)
Variable xs : alayout -> astate -> list (Z * Z).
Hypothesis HAX : forall inst ly S W mem md, ARX inst ly S W mem md ->
  layout_ok ly /\ sec_chunks_ok mmax S /\ ledger_cover im_segs ly md (sec_extents ly S ++ xs ly S) /\ amwf md /\
  Z.of_nat (length (st_sec_arr S)) + Z.of_nat (length (xs ly S)) <= lim /\
  Forall (fun e => 0 <= snd e <= nob) (xs ly S).

Theorem ifs_grant_w_P : AGif4.ifs_grant_w ARX nob.
Proof.
intros inst ly S W mem md mat sz HA Hsz.
destruct (HAX inst ly S W mem md HA) as (LY & SC & LC & MW & LIVE & XS).
pose proof (amwf_wvb md mat MW) as [_ NZ].
exact (sec_grant_exists_live_P nob lim mmax im_segs ly S (with_vm_backing (m_vm_lazy md) mat md) (xs ly S) sz
  HN HNal HW HSZ LY (ledger_cover_wvb im_segs ly md _ mat LC) NZ SC LIVE XS Hsz).
Qed.
End P.

(* At a unit's CfParams. *)
Section C.
Context {CF : CfParams}.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable xs : alayout -> astate -> list (Z * Z).
Hypothesis HAX : forall inst ly S W mem md, ARX inst ly S W mem md ->
  layout_ok ly /\ sec_chunks_ok cf_malloc_max S /\ ledger_cover im_segs ly md (sec_extents ly S ++ xs ly S) /\ amwf md /\
  Z.of_nat (length (st_sec_arr S)) + Z.of_nat (length (xs ly S)) <= cf_place_limit /\
  Forall (fun e => 0 <= snd e <= cf_nob) (xs ly S).

Theorem ifs_grant_w_cf : AGif4.ifs_grant_w ARX cf_nob.
Proof. exact (ifs_grant_w_P ARX cf_nob cf_place_limit cf_malloc_max cf_nob_lo cf_nob_al cf_place_ok cf_sizes_ok xs HAX). Qed.
End C.
End W.
