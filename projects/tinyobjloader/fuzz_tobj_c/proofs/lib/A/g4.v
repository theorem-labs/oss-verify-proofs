(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz Start8M.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess Uapi Syscall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR.

(* [comment removed for export] *)
Module Start8.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8M.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.StartNodes3E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.MuslMalloc40 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8StatesA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.Start8StatesB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac klia := unfold kHighMemBeg in *; repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end; lia.
Ltac blia := unfold SHADOW_BAND_LO, SHADOW_BAND_HI, SHADOW_RW_LO_END, SHADOW_RW_HI_BEG, kHighMemBeg in *; lia.

Section Seg8.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : vm_reserved (m_vmmaps m) = segments_reserved segsA.
Hypothesis Hmaps : vm_maps (m_vmmaps m) = [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000);
  (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000); (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000); (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)].
Hypothesis Hna : vm_noaccess (m_vmmaps m) = [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)].
Hypothesis Hlz : m_vm_lazy m = lazy_interior (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000)
  ++ lazy_interior (Z_to_bv 64 0x8fff7000) (Z_to_bv 64 0x20000000000) ++ lazy_interior (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000).
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : 0x646000 <= bv_unsigned a1 /\ (bv_unsigned a1 + 0x10000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a1)
  /\ bv_unsigned a1 + 0x10000 <= alloc_top (m_vmmaps m).
Hypothesis Ha2 : 0x646000 <= bv_unsigned a2 /\ (bv_unsigned a2 + 0x38e000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a2)
  /\ bv_unsigned a2 + 0x38e000 <= alloc_top (m_vmmaps m).
Hypothesis HBlim : B + 0x1000000 <= vm_limit (m_vmmaps m).
Hypothesis Hsb : vm_start_brk (m_vmmaps m) = vm_brk (m_vmmaps m).
Hypothesis Hbrk : 0x646000 <= bv_unsigned (vm_brk (m_vmmaps m)) <= 0x80646000.
Hypothesis Hbal : (4096 | bv_unsigned (vm_brk (m_vmmaps m))).
Variable ok : assn.
Hypothesis OKF : forall J : jpredA, (forall rho tp tr md, J rho tp tr md -> tr = []) -> ok_frameA segsA ok J.
Hypothesis OKP : forall J : jpredA, (forall rho tp tr md, J rho tp tr md -> tr = []) -> ok_pframeA segsA ok J.
Variables (P b4 b5 b6 : word).
Hypothesis HPL : mmap_place_ok_none (Z_to_bv 64 0) m n7 P.
Hypothesis HPL4 : mmap_place_ok_none (Z_to_bv 64 0) (m8 m P) n9 b4.
Hypothesis HPL5 : mmap_place_ok_none (Z_to_bv 64 0) (m9 m P b4) (Z_to_bv 64 4096) b5.
Hypothesis HPL6 : mmap_place_ok_none (Z_to_bv 64 0) (m10 m P b4 b5) (Z_to_bv 64 65536) b6.
Variables (b7 b8 b9 : word).
Hypothesis HPL7 : mmap_place_ok_none (Z_to_bv 64 0) (m11 m P b4 b5 b6) (Z_to_bv 64 4096) b7.
Hypothesis HPL8 : mmap_place_ok_none (Z_to_bv 64 0) (m12 m P b4 b5 b6 b7) (Z_to_bv 64 4096) b8.
Hypothesis HPL9 : mmap_place_ok_none (Z_to_bv 64 0) (m13 m P b4 b5 b6 b7 b8) (Z_to_bv 64 4096) b9.
Variables (x : Z) (b10 : word).
Hypothesis Hx : 0x7fff80000000 <= x <= 2 ^ 47.
Hypothesis H16 : x mod 16 = 0.
Hypothesis Hxtop : alloc_top (m_vmmaps m) = x - 8388608.
Hypothesis HPL10 : mmap_place_ok_none (Z_to_bv 64 0) (m16 m P b4 b5 b6 b7 b8 b9 x) (Z_to_bv 64 n17) b10.

Local Notation mE := (Start7.mE m P b4 b5 b6 b7 b8 b9 x b10).
Local Notation TOPz := (Start7.TOPz x).
Local Notation Q18 := (Start7.Q18 x).
Local Notation vals := (Start7.vals m a1 a2 P b4 b5 b6).
Local Notation TP18 := (Start7.TP18 x).
Local Notation B18 := (Start7.B18 B).
Local Notation r6of := (Start7.r6of).
Local Notation LmE := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out.LmE m P b4 b5 b6 b7 b8 b10).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation blocks16 := (Start6.blocks16 m a1 a2 Hres Hmaps Htop Ha1 Ha2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation priZ_facts := (Start6.priZ_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL) (only parsing).
Local Notation Upri := (Start6.Upri m a1 a2 P b4 b5 b6) (only parsing).
Local Notation CAx := (Start7.CAx x Hx H16) (only parsing).
Local Notation b10_facts := (Start7.b10_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxtop HPL10) (only parsing).
Local Notation blocks18_maps := (Start7.blocks18_maps m a1 a2 Hres Hmaps Htop Ha1 Ha2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16 Hxtop) (only parsing).
Local Notation TP18_range := (Start7.TP18_range m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 x Hx H16 Hxtop) (only parsing).
Local Notation TP17_le := (Start7.TP17_le m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 x Hx H16 Hxtop) (only parsing).
Local Notation maps_mE_eq := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out.maps_mE_eq m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10) (only parsing).

Variables (mo : Model) (L0 : list (word * word)).
Hypothesis HMI : minv8 L0 (vm_limit (m_vmmaps m)) (vm_init_sp (m_vmmaps m)) Q18 mo.
Hypothesis HL0 : forall e, In e LmE -> In e L0.

Local Notation limv := (vm_limit (m_vmmaps m)).
Local Notation ispv := (vm_init_sp (m_vmmaps m)).

Lemma OKFx : forall mx Bx, ok_frameA segsA ok (KxA mx Bx).
Proof. clear - OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.

Lemma isp_val : bv_unsigned ispv = x.
Proof. clear - Hxtop. unfold alloc_top in Hxtop. rewrite stack_max_size_val in Hxtop. lia. Qed.

Lemma B18_lim : B18 + 1048576 + 4 * 4096 <= limv.
Proof. clear - HBlim. unfold Start7.B18, Start7.B18pre, Start7.BE, B17, B16L, B16, BF, B12x, B12, B11, n17. lia. Qed.

Lemma Q18_facts : 0x10006fef8000 + 1048576 <= Q18 /\ Q18 <= SHADOW_BAND_HI /\ Q18 mod 4096 = 0.
Proof.
  clear - Hx H16. pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & _).
  unfold Start7.Q18, SHADOW_BAND_HI. repeat split; lia.
Qed.

Definition rhoOK (rho : valuation) : Prop :=
  vals rho /\ rw rho 36%positive = b7 /\ rw rho 77%positive = b8 /\ rw rho 78%positive = b9 /\ rw rho 83%positive = b10
  /\ x1 rho = x /\ 8 * bv_unsigned (rw rho 35%positive) = bv_unsigned b6
  /\ x + 80 <= r6of rho /\ r6of rho + 16 <= 2 ^ 47 /\ r6of rho + 16 <= x + 2238671.

Lemma rhoOK_agree : forall n rho rho', (86 <= n)%positive -> rhoOK rho -> (forall i, (i < n)%positive -> rw rho' i = rw rho i) -> rhoOK rho'.
Proof.
  clear. intros n rho rho' Hn (HV & H36 & H77 & H78 & H83 & Hx1 & V35 & H1 & H2 & H3) Hag.
  unfold rhoOK, x1, Start7.r6of in *. rewrite !Hag by lia.
  split; [eapply (vals12_agree _ _ _ _ _ _ _ n rho rho'); [lia | exact HV | intros i Hi; apply Hag; exact Hi]|].
  repeat split; assumption.
Qed.

Lemma rhoOK_v1 : forall rho, rhoOK rho -> bv_unsigned (rw rho 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m)).
Proof. clear. intros rho ((_ & _ & _ & _ & _ & _ & _ & _ & Hv1) & _). exact Hv1. Qed.

Lemma blocks18_band : forall rho, rhoOK rho -> forall e sz, In (e, sz) G18 ->
  (bv_unsigned (eval rho e) + sz <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned (eval rho e))
  \/ SHADOW_RW_HI_BEG <= bv_unsigned (eval rho e)
  \/ (e = SLit LOWPG /\ sz = 0x4c00).
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10.
  intros rho (HV & H36 & H77 & H78 & H83 & _) e sz Hin. pose proof b10_facts as (_ & L2 & _).
  unfold G18, G17 in Hin. rewrite !in_app_iff in Hin. destruct Hin as [[Hin|[[= <- <-]|[]]]|[[= <- <-]|[]]].
  - assert (Hin' : In (e, sz) G14b) by (unfold G14b; apply in_app_iff; left; exact Hin).
    destruct (blocks16 rho HV H36 H77 H78 e sz Hin') as [Hb|(_ & _ & _ & Hl)]; [left; exact Hb | right; left; unfold SHADOW_RW_HI_BEG; exact Hl].
  - right. right. split; reflexivity.
  - left. cbn [eval]. rewrite H83. exact L2.
Qed.

Lemma blocks18_pages : forall rho, rhoOK rho -> forall e sz, In (e, sz) G18 ->
  forall y, (0x7fffc000 <= y < 0x7fffc000 + 4096 \/ 0x80015000 <= y < 0x80015000 + 4096) ->
  ~ (bv_unsigned (eval rho e) <= y < bv_unsigned (eval rho e) + sz).
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10.
  intros rho HR e sz Hin y Hy. destruct (blocks18_band rho HR e sz Hin) as [Hb|[Hh|[-> ->]]]; [blia | blia |].
  cbn [eval]. unfold LOWPG. rewrite u64_of_lit by lia. lia.
Qed.

Lemma blocks22 : forall (mx : Model) rho (LB : Z), (forall e, In e LmE -> In e (vm_maps (m_vmmaps mx))) -> rhoOK rho ->
  forall e sz, In (e, sz) G18 ->
    (exists b s, In (b, s) (vm_maps (m_vmmaps mx)) /\ bv_unsigned b <= bv_unsigned (eval rho e) /\ bv_unsigned (eval rho e) + sz <= bv_unsigned b + bv_unsigned s)
    \/ bv_unsigned (eval rho e) + sz <= LB.
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10.
  intros mx rho LB HK (HV & H36 & H77 & H78 & H83 & _) e sz Hin. left.
  destruct (blocks18_maps rho HV H36 H77 H83 e sz Hin) as (b & s & Hm & B1 & B2 & B3).
  exists b, s. split; [apply HK; rewrite <- maps_mE_eq; exact Hm | lia].
Qed.

Lemma TP18_facts : forall rho, rhoOK rho -> forall p, In p (TP18 rho) ->
  0x800bc000 <= bv_unsigned p /\ bv_unsigned p + 4096 <= SHADOW_BAND_HI.
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10.
  intros rho HR p Hp. pose proof HR as (HV & H36 & H77 & H78 & H83 & Hx1 & V35 & H1 & H2 & H3).
  pose proof (Start7.arith18 x Hx H16 _ H1 H2 H3) as AR.
  destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A14 & _ & _ & A17 & A18 & _ & _ & _ & A22 & A23 & _).
  pose proof HV as (_ & _ & _ & _ & H31 & _ & _ & H34 & Hv1).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & CLIM & CLIM0 & CPB & CLEN & Ce12al).
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4).
  pose proof (Start6.sbZ_facts' m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 rho HV V35) as SB1. rewrite Hx1 in PR1, SB1.
  pose proof b6_facts as (F6lo & _). unfold x1 in Hx1. unfold SHADOW_BAND_HI.
  assert (T11 : forall q, In q (TP11 rho) -> 0x800bc000 <= bv_unsigned q /\ bv_unsigned q + 4096 <= 0x10007fff8000).
  { intros q Hq. unfold TP11 in Hq. pose proof (Upri rho HV) as UP. pose proof (urange (rw rho 35%positive)) as U35.
    assert (Hpri : 0x2008fff7000 <= priZ rho /\ priZ rho + 12288 + 4096 <= PEz x) by lia.
    assert (Hq1 : 0x800bc000 <= q1Z rho /\ q1Z rho + 12288 + 4096 <= PEz x).
    { unfold q1Z, sbZ in *. pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 35%positive) + 2147450880) 4096 ltac:(lia)). split; lia. }
    destruct (q1Z rho =? priZ rho); repeat (destruct Hq as [<-|Hq]; [first [rewrite u64_of_lit by lia | rewrite UP]; lia|]); destruct Hq. }
  assert (T12 : forall q, In q (TP12 rho) -> 0x800bc000 <= bv_unsigned q /\ bv_unsigned q + 4096 <= 0x10007fff8000).
  { intros q Hq. unfold TP12 in Hq. apply in_app_iff in Hq as [Hq|Hq]; [|exact (T11 q Hq)].
    apply In_pages_rev in Hq as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. unfold pageZ.
    unfold n12, q12, e12, shZ in *. rewrite Hx1 in *.
    pose proof (pagedown_props (x / 8 + 2147450880 - 131072)) as [AQ RQ]. pose proof (pagedown_props (x / 8 + 2147450880 - 9)) as [AE RE].
    set (q := x / 8 + 2147450880 - 131072 - (x / 8 + 2147450880 - 131072) mod 4096) in *.
    set (e := x / 8 + 2147450880 - 9 - (x / 8 + 2147450880 - 9) mod 4096) in *.
    assert (Hxd : 0x7fff80000000 / 8 <= x / 8 <= 2 ^ 47 / 8) by (split; apply Z.div_le_mono; lia).
    change (0x7fff80000000 / 8) with 17591917608960 in Hxd. change (2 ^ 47 / 8) with 17592186044416 in Hxd.
    assert (Hk' : Z.of_nat k <= (e - q) / 4096).
    { rewrite Z2Nat.id in Hk; [lia|]. apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia]. }
    assert (4096 * ((e - q) / 4096) <= e - q) by (apply Z.mul_div_le; lia).
    rewrite u64_of_lit by lia. split; [lia|]. Z.to_euclidean_division_equations; lia. }
  assert (T16 : forall q, In q (TP16 rho) -> 0x800bc000 <= bv_unsigned q /\ bv_unsigned q + 4096 <= 0x10007fff8000).
  { intros q Hq. unfold TP16 in Hq. unfold x1 in Hq. rewrite Hx1 in Hq.
    destruct (n16_val x Hx H16) as [N16 N16b]. destruct (site_arith x Hx H16) as (_ & SQlo & _ & _ & SQPE & _).
    pose proof (class_arith x Hx H16) as CAq. cbv zeta in CAq.
    destruct CAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CPEHPq & CHPloq & CPEhiq & _).
    apply in_app_iff in Hq as [Hq|Hq].
    - apply In_pages_rev in Hq as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. unfold pageZ. rewrite u64_of_lit by lia. lia.
    - apply In_enspage_inv in Hq as [->|Hq]; [rewrite u64_of_lit by lia; lia | exact (T12 q Hq)]. }
  assert (T17 : forall q, In q (TP17 rho) -> 0x800bc000 <= bv_unsigned q /\ bv_unsigned q + 4096 <= 0x10007fff8000).
  { intros q Hq. apply In_TP17 in Hq as [(k & Hk & _ & Uk)|Hq]; [rewrite Uk; unfold LOWPG; lia | exact (T16 q Hq)]. }
  unfold Start7.TP18 in Hp. destruct (Start7.nE x (r6of rho)) as [|k] eqn:EN.
  - cbn [Nat.eqb] in Hp. exact (T17 p Hp).
  - cbn [Nat.eqb] in Hp. specialize (A23 ltac:(discriminate)). unfold Start7.Q18, kHighMemBeg in *. apply in_app_iff in Hp as [Hp|Hp].
    + apply In_pages_rev in Hp as (k' & Hk' & ->). unfold pageZ. apply Nat2Z.inj_lt in Hk'. rewrite Nat2Z.inj_sub in Hk' by lia. change (Z.of_nat 1) with 1 in Hk'.
      rewrite u64_of_lit by lia. lia.
    + apply In_enspage_inv in Hp as [->|Hp]; [rewrite u64_of_lit by lia; lia | exact (T17 p Hp)].
Qed.

Lemma run22_safe : forall rho tp,
  triple segsA ok (SPA segsA (KxA mo B18) K18 rho tp)
    (fun w => exists v rho1, agree_below 159%positive rho rho1 /\ SPA segsA (KxA mo B18) (E22_of v) rho1 tp w).
Proof.
  clear - OKF. intros rho tp.
  eapply (@triple_conseq segsA ok (SPA segsA (KxA mo B18) K18x rho tp)); [intros w Hw; apply SPA_x_sub; [intros r [] | exact Hw] | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact run22 | apply OKFx | reflexivity | apply stableA_KxA]. }
  intros w (L & rho1 & Hin & Hag & Hsm & Hk). pose proof K18x_at as (N & _). rewrite N in Hag.
  destruct Hin as [<-|[<-|[]]]; cbn [la_state] in Hsm.
  - exists true, rho1. split; [exact Hag | split; [exact Hsm | exact Hk]].
  - exists false, rho1. split; [exact Hag | split; [exact Hsm | exact Hk]].
Qed.

Lemma erun22 : forall rho tp,
  etriple segsA (SPA segsA (KxA mo B18) K18 rho tp)
    (fun w => exists v rho1, agree_below 159%positive rho rho1 /\ SPA segsA (KxA mo B18) (E22_of v) rho1 tp w).
Proof.
  clear. intros rho tp.
  eapply (@etriple_conseq segsA (SPA segsA (KxA mo B18) K18x rho tp)); [intros w Hw; apply SPA_x_sub; [intros r [] | exact Hw] | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run22]. }
  intros w (L & rho1 & Hin & Hag & Hsm & Hk). pose proof K18x_at as (N & _). rewrite N in Hag.
  destruct Hin as [<-|[<-|[]]]; cbn [la_state] in Hsm.
  - exists true, rho1. split; [exact Hag | split; [exact Hsm | exact Hk]].
  - exists false, rho1. split; [exact Hag | split; [exact Hsm | exact Hk]].
Qed.

Lemma clear22 : forall v, objs_clear_e G18 (ax_S (E22_of v)) = true.
Proof. clear. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition m22 (b12 : word) : Model := eager_model 1048576 mo b12.
Definition L22 (b12 : word) : list (word * word) := (b12, Z_to_bv 64 1048576) :: L0.
Definition B22a : Z := B18 + 1048576.

Lemma node22 : forall v rho tp, rhoOK rho ->
  triple segsA ok (SPA segsA (KxA mo B18) (E22_of v) rho tp)
    (fun w => exists b12, mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) b12
              /\ LQA segsA (KxA (m22 b12) B22a) 160%positive (rho_set_rw rho 159%positive b12) tp [mkLeafA (E23_of v) RsCut] w).
Proof.
  intros v rho tp HR. pose proof (mi_res HMI) as MR. pose proof (mi_lim HMI) as ML. pose proof (mi_isp HMI) as MB.
  pose proof (E22_at v) as (P1 & N1 & EC & X1 & BS & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP (E22_of v) 1048576 mo B18 G18 160%positive X1 BS EC R17 R10 R11 R12 R13 R14 R15
             eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite N1; reflexivity) (clear22 v) MR (mi_top HMI) (minv8_bandM _ _ _ _ _ HMI)).
    + rewrite ML. pose proof B18_lim. lia.
    + exact (blocks22 mo rho _ (fun e He => minv8_in _ _ _ _ _ e HMI (HL0 e He)) HR).
    + rewrite MB. exact (rhoOK_v1 rho HR). }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA mo B18) (OKFx _ _) (fun n => stableA_KxA segsA n mo B18) _ (SPIN22_of v) 300%nat SPIN_MMAPORDIE);
      [destruct v; reflexivity | destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (run22_fail v) | exact (spin22 v)].
  - apply triple_ex; intros b12. apply triple_pure; intros HPL12.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b12; split; [exact HPL12|exact Hw] |].
    apply triple1_triple. rewrite N1. replace (eager_ok (E22_of v) 1048576 160%positive) with (S22ok_of v) by (symmetry; exact (S22ok_eq v)).
    unfold m22, B22a. assert (N2 : ss_next (ax_S (S22ok_of v)) = 160%positive) by (destruct v; reflexivity). rewrite <- N2.
    eapply sym_run_soundA; [exact (run23 v) | apply OKFx | destruct v; reflexivity | apply stableA_KxA].
Qed.

Hypothesis Hwit22 : exists a, mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) a.

Lemma enode22 : forall v rho tp, rhoOK rho ->
  etriple segsA (SPA segsA (KxA mo B18) (E22_of v) rho tp)
    (fun w => exists b12, mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) b12
              /\ LQA segsA (KxA (m22 b12) B22a) 160%positive (rho_set_rw rho 159%positive b12) tp [mkLeafA (E23_of v) RsCut] w).
Proof.
  intros v rho tp HR. pose proof (mi_res HMI) as MR. pose proof (mi_lim HMI) as ML. pose proof (mi_isp HMI) as MB.
  pose proof (E22_at v) as (P1 & N1 & EC & X1 & BS & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  eapply etriple_seq.
  { apply (eager_rw_enode (E22_of v) 1048576 mo B18 G18 160%positive X1 BS EC R17 R10 R11 R12 R13 R14 R15
             eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite N1; reflexivity) (clear22 v) MR (mi_top HMI) (minv8_bandM _ _ _ _ _ HMI)).
    + rewrite ML. pose proof B18_lim. lia.
    + exact Hwit22.
    + exact (blocks22 mo rho _ (fun e He => minv8_in _ _ _ _ _ e HMI (HL0 e He)) HR).
    + rewrite MB. exact (rhoOK_v1 rho HR). }
  apply etriple_ex; intros b12. apply etriple_pure; intros HPL12.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b12; split; [exact HPL12|exact Hw] |].
  rewrite N1. replace (eager_ok (E22_of v) 1048576 160%positive) with (S22ok_of v) by (symmetry; exact (S22ok_eq v)).
  unfold m22, B22a. assert (N2 : ss_next (ax_S (S22ok_of v)) = 160%positive) by (destruct v; reflexivity). rewrite <- N2.
  eapply sym_run_etripleA; [destruct v; reflexivity | apply stableA_KxA | exact (run23 v)].
Qed.

Definition G22b : list (sv * Z) := G18 ++ [(SVar 159%positive, 1048576)].
Lemma clear23 : forall v, objs_clear_e G22b (ax_S (E23_of v)) = true.
Proof. clear. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition m23a (b12 b13 : word) : Model := null_rw_model 8388608 (m22 b12) b13.
Definition L23 (b12 b13 : word) : list (word * word) := (b13, Z_to_bv 64 8388608) :: L22 b12.

Definition rho23 (rho : valuation) (a : word) : valuation := rho_set_rw (set_rm rho (unmap_range (rm rho) a (Z_to_bv 64 8388608))) 160%positive a.

Lemma rm_rho23 : forall rho b13 (a : word), ~ (bv_unsigned b13 <= bv_unsigned a < bv_unsigned b13 + 8388608) -> rm (rho23 rho b13) a = rm rho a.
Proof.
  clear. intros rho b13 a Ha. unfold rho23. rewrite rho_set_rw_rm. cbn [rm set_rm]. rewrite unmap_range_at.
  destruct (SysStep.in_range b13 (Z_to_bv 64 8388608) a) eqn:E; [|reflexivity]. apply SysStep.in_range_spec in E. rewrite u64_of_lit in E by lia. exfalso. exact (Ha E).
Qed.

Section S22.
Variable b12 : word.
Hypothesis HPL12 : mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) b12.

Lemma MI22 : minv8 (L22 b12) limv ispv Q18 (m22 b12)
  /\ 0x646000 <= bv_unsigned b12 /\ (bv_unsigned b12 + 1048576 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b12)
  /\ bv_unsigned b12 mod 4096 = 0 /\ bv_unsigned b12 + 1048576 <= TOPz.
Proof.
  clear - HMI HPL12 Hxtop.
  pose proof (minv8_place _ _ _ _ _ 1048576 b12 HMI ltac:(lia) eq_refl ltac:(lia) HPL12) as (P1 & P2 & P3 & P4 & P5 & _).
  change (LB_of 1048576) with 0x646000 in P1. pose proof isp_val as UI. rewrite UI in P4.
  split; [|unfold Start7.TOPz; repeat split; assumption].
  unfold L22, m22. apply (minv8_eager _ _ _ _ mo 1048576 b12 HMI); [lia | reflexivity | lia | exact HPL12].
Qed.

Lemma blocks23 : forall rho (LB : Z), rhoOK rho -> rw rho 159%positive = b12 ->
  forall e sz, In (e, sz) G22b ->
    (exists b s, In (b, s) (vm_maps (m_vmmaps (m22 b12))) /\ bv_unsigned b <= bv_unsigned (eval rho e) /\ bv_unsigned (eval rho e) + sz <= bv_unsigned b + bv_unsigned s)
    \/ bv_unsigned (eval rho e) + sz <= LB.
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10 HMI HL0 HPL12.
  intros rho LB HR H159 e sz Hin. pose proof MI22 as (MI & _).
  unfold G22b in Hin. apply in_app_iff in Hin as [Hin|[[= <- <-]|[]]].
  - apply (blocks22 (m22 b12) rho LB); [|exact HR | exact Hin]. intros e' He'. apply (minv8_in _ _ _ _ _ e' MI). unfold L22. right. exact (HL0 e' He').
  - left. exists b12, (Z_to_bv 64 1048576). cbn [eval]. rewrite H159. split; [apply (minv8_in _ _ _ _ _ _ MI); unfold L22; left; reflexivity|].
    rewrite u64_of_lit by lia. lia.
Qed.

Lemma prepay23 : forall v rho tp b13 ms md, rhoOK rho -> rw rho 159%positive = b12 ->
  (forall p, In p tp -> 0x800bc000 <= bv_unsigned p /\ bv_unsigned p + 4096 <= SHADOW_BAND_HI) ->
  mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) b13 ->
  SPA segsA (KxA (m23a b12 b13) B22a) (S23ok0_of v) (rho23 rho b13) tp ([], mkCfg ms md) ->
  SPA segsA (KxA (m23a b12 b13) (B22a + 4096)) (S23ok_of v) (rho23 rho b13) (b13 :: tp) ([], mkCfg ms md).
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10 HMI HL0 HPL12.
  intros v rho tp b13 ms md HR H159 Htp HPL13 Hsp. pose proof MI22 as (MI & _). pose proof (mi_res MI) as MR. pose proof (mi_lim MI) as ML.
  destruct (S23ok_eq v) as [EQ SB]. rewrite <- EQ.
  pose proof (minv8_place _ _ _ _ _ 8388608 b13 MI ltac:(lia) eq_refl ltac:(lia) HPL13) as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof isp_val as UI. rewrite UI in T4.
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid.
  pose proof (erase_mat_eq_fields md _ Hem) as (Evm & Elz & _).
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF.
  set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA (m23a b12 b13) (B22a + 4096) r (b13 :: tp) tr0 md0).
  assert (H2 : SPA segsA J' (S23ok0_of v) (rho23 rho b13) tp ([], mkCfg ms md)).
  { split; [exact Hsm|]. subst J'. cbv beta. split; [reflexivity|]. split; [exact Hem|]. cbn [w_cfg cfg_model snd].
    pose proof (paid_cons_le md b13 tp). unfold page_size in *. lia. }
  change (SPA segsA (KxA (m23a b12 b13) (B22a + 4096)) (ax_setS (S23ok0_of v) (set_objs (ax_S (S23ok0_of v)) (ss_objs (ax_S (S23ok0_of v)) ++ [o13p]))) (rho23 rho b13) (b13 :: tp) ([], mkCfg ms md))
    with (SPA segsA J' (ax_setS (S23ok0_of v) (set_objs (ax_S (S23ok0_of v)) (ss_objs (ax_S (S23ok0_of v)) ++ [o13p]))) (rho23 rho b13) (b13 :: tp) ([], mkCfg ms md)).
  unfold o13p. change (SLit 4096) with (SLit page_size).
  apply (SPA_prepay_zero_at segsA J' (rho23 rho b13) (S23ok0_of v) b13 (SVar 160%positive) tp [] ms md H2).
  - destruct v; reflexivity.
  - unfold page_size. exact T5.
  - rewrite Elz. unfold m23a. apply null_rw_first_page; [lia | reflexivity | lia | lia | exact T5 | pose proof Hx; unfold Start7.TOPz in T4; lia].
  - intros Hin. pose proof (Htp _ Hin). blia.
  - intros j Hj. rewrite Evm. unfold m23a, null_rw_model, vm_add_lazy. rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps. unfold null_rw_h. cbn [vm_noaccess].
    apply (minv8_fresh_acc _ _ _ _ _ b13 (Z_to_bv 64 8388608) _ MI T6). rewrite u64_of_lit by lia. unfold page_size in Hj. lia.
  - unfold headroom. rewrite Evm. unfold m23a, null_rw_model, vm_add_lazy. rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps. unfold null_rw_h. cbn [vm_limit].
    fold (m22 b12). rewrite ML. pose proof B18_lim. unfold B22a, page_size in *. lia.
  -
    cbn [ax_S]. apply Forall_forall. intros o Ho.
    assert (HGo : forall o', In o' (ss_objs (ax_S (E23_of v))) -> ranges_disjoint (obj_range (rho23 rho b13) o') (bv_unsigned b13, bv_unsigned b13 + 8388608)).
    { intros o' Ho'.
      assert (HFE : Forall (holds (rho23 rho b13)) (ss_facts (ax_S (E23_of v)))).
      { assert (EF : ss_facts (ax_S (S23ok0_of v)) = null_rw_facts (E23_of v) 8388608 ++ ss_facts (ax_S (E23_of v))) by (destruct v; reflexivity).
        rewrite EF in HF. apply Forall_app in HF as [_ HF']. exact HF'. }
      assert (HR' : rhoOK (rho23 rho b13)) by (apply (rhoOK_agree 160%positive rho); [lia | exact HR | intros i Hi; unfold rho23; rewrite rho_set_rw_other by lia; reflexivity]).
      apply (objs_clear_e_sound (rho23 rho b13) G22b (ax_S (E23_of v)) b13 8388608 HFE (clear23 v) ltac:(lia)); [| | |exact Ho'].
      - right. pose proof (rhoOK_v1 _ HR') as V1. rewrite V1, UI. unfold Start7.TOPz in T4. lia.
      - intros y Hy. apply (free_not_image8 _ b13 (Z_to_bv 64 8388608) T6); [rewrite u64_of_lit by lia; lia|]. rewrite u64_of_lit by lia. exact Hy.
      - intros e sz Hin y Hy.
        destruct (blocks23 (rho23 rho b13) 0 HR' ltac:(unfold rho23; rewrite rho_set_rw_other by lia; cbn; exact H159) e sz Hin) as [(b & s0 & Hm & B1 & B2)|Hlow];
          [|pose proof (urange (eval (rho23 rho b13) e)); intros HH; lia].
        rewrite (mi_maps MI) in Hm.
        pose proof (State.region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ T6) Hm) as OV.
        unfold iv_overlap in OV. rewrite (u64_of_lit 8388608) in OV by lia. apply andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
    assert (Ho' : In o (ss_objs (ax_S (E23_of v)))) by (destruct v; exact Ho).
    pose proof (HGo o Ho') as D. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. unfold page_size. lia.
  - exact SB.
  - cbn [eval]. unfold rho23. apply rho_set_rw_at.
  - intros X; exact X.
Qed.

Lemma node23 : forall v rho tp, rhoOK rho -> rw rho 159%positive = b12 ->
  (forall p, In p tp -> 0x800bc000 <= bv_unsigned p /\ bv_unsigned p + 4096 <= SHADOW_BAND_HI) ->
  triple segsA ok (SPA segsA (KxA (m22 b12) B22a) (E23_of v) rho tp)
    (fun w => exists b13, mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) b13
              /\ LQA segsA (KxA (m23a b12 b13) (B22a + 4096)) 161%positive (rho23 rho b13) (b13 :: tp) [mkLeafA (E24_of v) RsCut] w).
Proof.
  intros v rho tp HR H159 Htp. pose proof MI22 as (MI & _). pose proof (mi_res MI) as MR. pose proof (mi_lim MI) as ML. pose proof (mi_isp MI) as MB.
  pose proof (E23_at v) as (P1 & N1 & EC & X1 & BS & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  eapply triple_seq.
  { apply triple1_triple.
    apply (lazy_null_rw_node ok OKF OKP (E23_of v) 8388608 (m22 b12) B22a G22b 161%positive X1 BS EC R17 R10 R11 R12 R13 R14 R15
             eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite N1; reflexivity) (clear23 v) MR (mi_top MI) (minv8_bandM _ _ _ _ _ MI) rho23).
    + intros rho0 a. rewrite N1. unfold rho23. apply agree_below_set_rw. lia.
    + intros rho0 a. rewrite N1. unfold rho23. apply rho_set_rw_at.
    + exact (blocks23 rho _ HR H159).
    + rewrite MB. exact (rhoOK_v1 rho HR). }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m22 b12) B22a) (OKFx _ _) (fun n => stableA_KxA segsA n (m22 b12) B22a) _ (SPIN23_of v) 300%nat SPIN_MMAPORDIE);
      [destruct v; reflexivity | destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (run23_fail v) | exact (spin23 v)].
  - apply triple_ex; intros b13. apply triple_pure; intros HPL13.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b13; split; [exact HPL13|exact Hw] |].
    replace (null_rw_ok (E23_of v) 8388608 161%positive) with (S23ok0_of v) by (symmetry; exact (S23ok0_eq v)).
    eapply (@triple_conseq segsA ok (SPA segsA (KxA (m23a b12 b13) (B22a + 4096)) (S23ok_of v) (rho23 rho b13) (b13 :: tp))); [| intros w Hw; exact Hw |].
    { intros [tr [ms md]] Hsp. pose proof Hsp as [_ (Htr & _)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr. subst tr. exact (prepay23 v rho tp b13 ms md HR H159 Htp HPL13 Hsp). }
    apply triple1_triple. assert (N2 : ss_next (ax_S (S23ok_of v)) = 161%positive) by (destruct v; reflexivity). rewrite <- N2.
    eapply sym_run_soundA; [exact (run24 v) | apply OKFx | destruct v; reflexivity | apply stableA_KxA].
Qed.

Hypothesis Hw23 : exists a, mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) a.

Lemma enode23 : forall v rho tp, rhoOK rho -> rw rho 159%positive = b12 ->
  (forall p, In p tp -> 0x800bc000 <= bv_unsigned p /\ bv_unsigned p + 4096 <= SHADOW_BAND_HI) ->
  etriple segsA (SPA segsA (KxA (m22 b12) B22a) (E23_of v) rho tp)
    (fun w => exists b13, mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) b13
              /\ LQA segsA (KxA (m23a b12 b13) (B22a + 4096)) 161%positive (rho23 rho b13) (b13 :: tp) [mkLeafA (E24_of v) RsCut] w).
Proof.
  intros v rho tp HR H159 Htp. pose proof MI22 as (MI & _). pose proof (mi_res MI) as MR. pose proof (mi_lim MI) as ML. pose proof (mi_isp MI) as MB.
  pose proof (E23_at v) as (P1 & N1 & EC & X1 & BS & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  eapply etriple_seq.
  { apply (lazy_null_rw_enode (E23_of v) 8388608 (m22 b12) B22a G22b 161%positive X1 BS EC R17 R10 R11 R12 R13 R14 R15
             eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite N1; reflexivity) (clear23 v) MR (mi_top MI) (minv8_bandM _ _ _ _ _ MI) rho23).
    + intros rho0 a. rewrite N1. unfold rho23. apply agree_below_set_rw. lia.
    + intros rho0 a. rewrite N1. unfold rho23. apply rho_set_rw_at.
    + exact Hw23.
    + exact (blocks23 rho _ HR H159).
    + rewrite MB. exact (rhoOK_v1 rho HR). }
  apply etriple_ex; intros b13. apply etriple_pure; intros HPL13.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b13; split; [exact HPL13|exact Hw] |].
  replace (null_rw_ok (E23_of v) 8388608 161%positive) with (S23ok0_of v) by (symmetry; exact (S23ok0_eq v)).
  eapply (@etriple_conseq segsA (SPA segsA (KxA (m23a b12 b13) (B22a + 4096)) (S23ok_of v) (rho23 rho b13) (b13 :: tp))); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] Hsp. pose proof Hsp as [_ (Htr & _)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr. subst tr. exact (prepay23 v rho tp b13 ms md HR H159 Htp HPL13 Hsp). }
  assert (N2 : ss_next (ax_S (S23ok_of v)) = 161%positive) by (destruct v; reflexivity). rewrite <- N2.
  eapply sym_run_etripleA; [destruct v; reflexivity | apply stableA_KxA | exact (run24 v)].
Qed.

Definition G23b : list (sv * Z) := G22b ++ [(SVar 160%positive, 8388608)].
Lemma clear24 : forall v, objs_clear_e G23b (ax_S (E24_of v)) = true.
Proof. clear. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition m24 (b12 b13 b14 : word) : Model := eager_model 4096 (m23a b12 b13) b14.
Definition L24 (b12 b13 b14 : word) : list (word * word) := (b14, Z_to_bv 64 4096) :: L23 b12 b13.
Definition B24 : Z := B22a + 4096 + 4096.

Section S23.
Variable b13 : word.
Hypothesis HPL13 : mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) b13.

Lemma MI23 : minv8 (L23 b12 b13) limv ispv Q18 (m23a b12 b13)
  /\ 0x646000 <= bv_unsigned b13 /\ (bv_unsigned b13 + 8388608 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b13)
  /\ bv_unsigned b13 mod 4096 = 0 /\ bv_unsigned b13 + 8388608 <= TOPz.
Proof.
  clear - HMI HPL12 HPL13 Hxtop.
  pose proof MI22 as (MI & _).
  pose proof (minv8_place _ _ _ _ _ 8388608 b13 MI ltac:(lia) eq_refl ltac:(lia) HPL13) as (P1 & P2 & P3 & P4 & P5 & _).
  change (LB_of 8388608) with 0x646000 in P1. pose proof isp_val as UI. rewrite UI in P4.
  split; [|unfold Start7.TOPz; repeat split; assumption].
  unfold L23, m23a. apply (minv8_null_rw _ _ _ _ (m22 b12) 8388608 b13 MI); [lia | reflexivity | lia | exact HPL13].
Qed.

Lemma blocks24 : forall rho (LB : Z), rhoOK rho -> rw rho 159%positive = b12 -> rw rho 160%positive = b13 ->
  forall e sz, In (e, sz) G23b ->
    (exists b s, In (b, s) (vm_maps (m_vmmaps (m23a b12 b13))) /\ bv_unsigned b <= bv_unsigned (eval rho e) /\ bv_unsigned (eval rho e) + sz <= bv_unsigned b + bv_unsigned s)
    \/ bv_unsigned (eval rho e) + sz <= LB.
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10 HMI HL0 HPL12 HPL13.
  intros rho LB HR H159 H160 e sz Hin. pose proof MI23 as (MI & _). pose proof (mi_maps MI) as MM.
  unfold G23b in Hin. apply in_app_iff in Hin as [Hin|[[= <- <-]|[]]].
  - destruct (blocks23 rho LB HR H159 e sz Hin) as [(b & s0 & Hm & B1 & B2)|Hlow]; [left | right; exact Hlow].
    exists b, s0. rewrite MM. rewrite (mi_maps (proj1 MI22)) in Hm. split; [unfold L23; right; exact Hm | lia].
  - left. exists b13, (Z_to_bv 64 8388608). cbn [eval]. rewrite H160, MM. split; [unfold L23; left; reflexivity|]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma node24 : forall v rho tp, rhoOK rho -> rw rho 159%positive = b12 -> rw rho 160%positive = b13 ->
  triple segsA ok (SPA segsA (KxA (m23a b12 b13) (B22a + 4096)) (E24_of v) rho tp)
    (fun w => exists b14, mmap_place_ok_none (Z_to_bv 64 0) (m23a b12 b13) (Z_to_bv 64 4096) b14
              /\ LQA segsA (KxA (m24 b12 b13 b14) B24) 162%positive (rho_set_rw rho 161%positive b14) tp [mkLeafA (EG_of v) RsCut] w).
Proof.
  intros v rho tp HR H159 H160. pose proof MI23 as (MI & _). pose proof (mi_res MI) as MR. pose proof (mi_lim MI) as ML. pose proof (mi_isp MI) as MB.
  pose proof (E24_at v) as (P1 & N1 & EC & X1 & BS & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP (E24_of v) 4096 (m23a b12 b13) (B22a + 4096) G23b 162%positive X1 BS EC R17 R10 R11 R12 R13 R14 R15
             eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite N1; reflexivity) (clear24 v) MR (mi_top MI) (minv8_bandM _ _ _ _ _ MI)).
    + rewrite ML. pose proof B18_lim. unfold B22a in *. lia.
    + exact (blocks24 rho _ HR H159 H160).
    + rewrite MB. exact (rhoOK_v1 rho HR). }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m23a b12 b13) (B22a + 4096)) (OKFx _ _) (fun n => stableA_KxA segsA n (m23a b12 b13) (B22a + 4096)) _ (SPIN24_of v) 300%nat SPIN_MMAPORDIE);
      [destruct v; reflexivity | destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (run24_fail v) | exact (spin24 v)].
  - apply triple_ex; intros b14. apply triple_pure; intros HPL14.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b14; split; [exact HPL14|exact Hw] |].
    apply triple1_triple. rewrite N1. replace (eager_ok (E24_of v) 4096 162%positive) with (S24ok_of v) by (symmetry; exact (S24ok_eq v)).
    unfold m24, B24. assert (N2 : ss_next (ax_S (S24ok_of v)) = 162%positive) by (destruct v; reflexivity). rewrite <- N2.
    eapply sym_run_soundA; [exact (runG v) | apply OKFx | destruct v; reflexivity | apply stableA_KxA].
Qed.

Hypothesis Hw24 : exists a, mmap_place_ok_none (Z_to_bv 64 0) (m23a b12 b13) (Z_to_bv 64 4096) a.

Lemma enode24 : forall v rho tp, rhoOK rho -> rw rho 159%positive = b12 -> rw rho 160%positive = b13 ->
  etriple segsA (SPA segsA (KxA (m23a b12 b13) (B22a + 4096)) (E24_of v) rho tp)
    (fun w => exists b14, mmap_place_ok_none (Z_to_bv 64 0) (m23a b12 b13) (Z_to_bv 64 4096) b14
              /\ LQA segsA (KxA (m24 b12 b13 b14) B24) 162%positive (rho_set_rw rho 161%positive b14) tp [mkLeafA (EG_of v) RsCut] w).
Proof.
  intros v rho tp HR H159 H160. pose proof MI23 as (MI & _). pose proof (mi_res MI) as MR. pose proof (mi_lim MI) as ML. pose proof (mi_isp MI) as MB.
  pose proof (E24_at v) as (P1 & N1 & EC & X1 & BS & R17 & R10 & R11 & R12 & R13 & R14 & R15).
  eapply etriple_seq.
  { apply (eager_rw_enode (E24_of v) 4096 (m23a b12 b13) (B22a + 4096) G23b 162%positive X1 BS EC R17 R10 R11 R12 R13 R14 R15
             eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite N1; reflexivity) (clear24 v) MR (mi_top MI) (minv8_bandM _ _ _ _ _ MI)).
    + rewrite ML. pose proof B18_lim. unfold B22a in *. lia.
    + exact Hw24.
    + exact (blocks24 rho _ HR H159 H160).
    + rewrite MB. exact (rhoOK_v1 rho HR). }
  apply etriple_ex; intros b14. apply etriple_pure; intros HPL14.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b14; split; [exact HPL14|exact Hw] |].
  rewrite N1. replace (eager_ok (E24_of v) 4096 162%positive) with (S24ok_of v) by (symmetry; exact (S24ok_eq v)).
  unfold m24, B24. assert (N2 : ss_next (ax_S (S24ok_of v)) = 162%positive) by (destruct v; reflexivity). rewrite <- N2.
  eapply sym_run_etripleA; [destruct v; reflexivity | apply stableA_KxA | exact (runG v)].
Qed.

Section S24.
Variable b14 : word.
Hypothesis HPL14 : mmap_place_ok_none (Z_to_bv 64 0) (m23a b12 b13) (Z_to_bv 64 4096) b14.

Lemma MI24 : minv8 (L24 b12 b13 b14) limv ispv Q18 (m24 b12 b13 b14)
  /\ 0x1000 <= bv_unsigned b14 /\ (bv_unsigned b14 + 4096 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b14)
  /\ bv_unsigned b14 mod 4096 = 0 /\ bv_unsigned b14 + 4096 <= TOPz.
Proof.
  clear - HMI HPL12 HPL13 HPL14 Hxtop.
  pose proof MI23 as (MI & _).
  pose proof (minv8_place _ _ _ _ _ 4096 b14 MI ltac:(lia) eq_refl ltac:(lia) HPL14) as (P1 & P2 & P3 & P4 & P5 & _).
  change (LB_of 4096) with 0x1000 in P1. pose proof isp_val as UI. rewrite UI in P4.
  split; [|unfold Start7.TOPz; repeat split; assumption].
  unfold L24, m24. apply (minv8_eager _ _ _ _ (m23a b12 b13) 4096 b14 MI); [lia | reflexivity | lia | exact HPL14].
Qed.

Definition G24 : list (sv * Z) := G23b ++ [(SVar 161%positive, 4096)].
Definition G24e : list (sv * Z) := G24 ++ [(SLit 0x7fffc000, 4096)].

Lemma blocks24_low : forall rho, rhoOK rho -> rw rho 159%positive = b12 -> rw rho 160%positive = b13 -> rw rho 161%positive = b14 ->
  forall e sz, In (e, sz) G24e -> forall y, (0x7fffc000 <= y < 0x7fffc000 + 4096 \/ 0x80015000 <= y < 0x80015000 + 4096) ->
  In (e, sz) G24 \/ 0x80015000 <= y -> ~ (bv_unsigned (eval rho e) <= y < bv_unsigned (eval rho e) + sz).
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10 HMI HL0 HPL12 HPL13 HPL14.
  intros rho HR H159 H160 H161 e sz Hin y Hy Hsel. pose proof MI24 as (_ & _ & P14 & _). pose proof MI23 as (_ & _ & P13 & _). pose proof MI22 as (_ & _ & P12 & _).
  unfold G24e, G24, G23b, G22b in Hin. rewrite !in_app_iff in Hin.
  destruct Hin as [[[[Hin|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]; cbn [eval].
  - exact (blocks18_pages rho HR e sz Hin y Hy).
  - rewrite H159. blia.
  - rewrite H160. blia.
  - rewrite H161. blia.
  - rewrite u64_of_lit by lia. destruct Hsel as [Hsel|Hsel]; [|lia].
    exfalso. unfold G24, G23b, G22b, G18, G17, G13b, G12b, G11c, ri30, shRI_base, LOWPG in Hsel. rewrite <- !app_assoc in Hsel. cbn [List.app In] in Hsel.
    repeat (destruct Hsel as [Hsel|Hsel]; [discriminate Hsel|]). exact Hsel.
Qed.

Lemma NIN24 : forall rho, rhoOK rho -> forall p, In p (b13 :: TP18 rho) -> bv_unsigned p <> 0x7fffc000 /\ bv_unsigned p <> 0x80015000.
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10 HMI HPL12 HPL13.
  intros rho HR p [<-|Hp]; [pose proof MI23 as (_ & _ & P13 & _); split; blia|].
  pose proof (TP18_facts rho HR p Hp) as [T1 T2]. split; lia.
Qed.

Lemma pay_pages : forall (Ca Ce Cg : sstate) rho ms md,
  rhoOK rho -> rw rho 159%positive = b12 -> rw rho 160%positive = b13 -> rw rho 161%positive = b14 ->
  set_objs Ca (ss_objs Ca ++ [zero_page_obj PGA]) = Ce -> same_but_objs Ca (set_objs Ca (ss_objs Ca ++ [zero_page_obj PGA])) = true ->
  set_objs Ce (ss_objs Ce ++ [zero_page_obj PGB]) = Cg -> same_but_objs Ce (set_objs Ce (ss_objs Ce ++ [zero_page_obj PGB])) = true ->
  objs_clear_e G24 Ca = true -> objs_clear_e G24e Ce = true ->
  SPA segsA (KxA (m24 b12 b13 b14) B24) (mkAX Ca [] (SLit SHB)) rho (b13 :: TP18 rho) ([], mkCfg ms md) ->
  SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) (mkAX Cg [] (SLit SHB)) rho (PGB :: PGA :: b13 :: TP18 rho) ([], mkCfg ms md).
Proof.
  clear - Hres Hmaps Htop Ha1 Ha2 HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hx H16 Hxtop HPL10 HMI HL0 HPL12 HPL13 HPL14.
  intros Ca Ce Cg rho ms md HR H159 H160 H161 EQe SBe EQg SBg CLa CLe Hsp.
  pose proof MI24 as (MI & P1 & P2 & P3 & P4). pose proof (mi_res MI) as MR. pose proof (mi_lim MI) as ML.
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid.
  pose proof (erase_mat_eq_fields md _ Hem) as (Evm & Elz & _).
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  pose proof (NIN24 rho HR) as NIN. pose proof isp_val as UI.
  assert (UA : bv_unsigned PGA = 0x7fffc000) by reflexivity. assert (UB : bv_unsigned PGB = 0x80015000) by reflexivity.
  assert (EFe : ss_facts Ce = ss_facts Ca) by (rewrite <- EQe; reflexivity).

  set (J1 := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA (m24 b12 b13 b14) (B24 + 4096) r (PGA :: b13 :: TP18 rho) tr0 md0).
  assert (H1 : SPA segsA J1 (mkAX Ca [] (SLit SHB)) rho (b13 :: TP18 rho) ([], mkCfg ms md)).
  { split; [exact Hsm|]. subst J1. cbv beta. split; [reflexivity|]. split; [exact Hem|]. cbn [w_cfg cfg_model snd].
    pose proof (paid_cons_le md PGA (b13 :: TP18 rho)). unfold page_size in *. lia. }
  assert (H2 : SPA segsA J1 (mkAX Ce [] (SLit SHB)) rho (PGA :: b13 :: TP18 rho) ([], mkCfg ms md)).
  { rewrite <- EQe. change (mkAX (set_objs Ca (ss_objs Ca ++ [zero_page_obj PGA])) [] (SLit SHB)) with
      (ax_setS (mkAX Ca [] (SLit SHB)) (set_objs (ax_S (mkAX Ca [] (SLit SHB))) (ss_objs (ax_S (mkAX Ca [] (SLit SHB))) ++ [zero_page_obj PGA]))).
    apply (SPA_prepay_zero segsA J1 rho (mkAX Ca [] (SLit SHB)) PGA (b13 :: TP18 rho) [] ms md H1).
    - reflexivity.
    - rewrite Elz. apply (mi_lzlow MI); rewrite UA; unfold SHADOW_BAND_LO, SHADOW_RW_LO_END; lia.
    - intros Hin. exact (proj1 (NIN _ Hin) UA).
    - intros j Hj. rewrite Evm. apply (mi_acclow MI). rewrite UA. unfold SHADOW_BAND_LO, SHADOW_RW_LO_END. unfold page_size in Hj. lia.
    - unfold headroom. rewrite Evm, ML. pose proof B18_lim. unfold B24, B22a, page_size in *. lia.
    - cbn [ax_S]. apply Forall_forall. intros o Ho. rewrite UA. unfold page_size.
      apply (objs_clear_e_sound rho G24 Ca PGA 4096 HF CLa ltac:(lia)); [rewrite UA; left; lia | rewrite UA; intros y Hy; lia | | exact Ho].
      rewrite UA. intros e sz Hin y Hy. apply (blocks24_low rho HR H159 H160 H161 e sz ltac:(unfold G24e; apply in_app_iff; left; exact Hin) y ltac:(lia) (or_introl Hin)).
    - intros X; exact X. }

  set (J2 := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA (m24 b12 b13 b14) (B24 + 8192) r (PGB :: PGA :: b13 :: TP18 rho) tr0 md0).
  assert (H3 : SPA segsA J2 (mkAX Ce [] (SLit SHB)) rho (PGA :: b13 :: TP18 rho) ([], mkCfg ms md)).
  { destruct H2 as [Hsm2 _]. split; [exact Hsm2|]. subst J2. cbv beta. split; [reflexivity|]. split; [exact Hem|]. cbn [w_cfg cfg_model snd].
    pose proof (paid_cons_le md PGB (PGA :: b13 :: TP18 rho)). pose proof (paid_cons_le md PGA (b13 :: TP18 rho)). unfold page_size in *. lia. }
  rewrite <- EQg.
  change (mkAX (set_objs Ce (ss_objs Ce ++ [zero_page_obj PGB])) [] (SLit SHB)) with
    (ax_setS (mkAX Ce [] (SLit SHB)) (set_objs (ax_S (mkAX Ce [] (SLit SHB))) (ss_objs (ax_S (mkAX Ce [] (SLit SHB))) ++ [zero_page_obj PGB]))).
  match goal with |- SPA _ _ ?A ?r ?t ?w => change (SPA segsA J2 A r t w) end.
  apply (SPA_prepay_zero segsA J2 rho (mkAX Ce [] (SLit SHB)) PGB (PGA :: b13 :: TP18 rho) [] ms md H3).
  - reflexivity.
  - rewrite Elz. apply (mi_lzlow MI); rewrite UB; unfold SHADOW_BAND_LO, SHADOW_RW_LO_END; lia.
  - intros [E|Hin]; [apply (f_equal bv_unsigned) in E; rewrite UA, UB in E; lia | exact (proj2 (NIN _ Hin) UB)].
  - intros j Hj. rewrite Evm. apply (mi_acclow MI). rewrite UB. unfold SHADOW_BAND_LO, SHADOW_RW_LO_END. unfold page_size in Hj. lia.
  - unfold headroom. rewrite Evm, ML. pose proof B18_lim. pose proof (paid_cons_le md PGA (b13 :: TP18 rho)). unfold B24, B22a, page_size in *. lia.
  - cbn [ax_S]. apply Forall_forall. intros o Ho. pose proof (SPA_facts_hold segsA _ _ _ _ _ H2) as HF2. cbn [ax_S] in HF2.
    rewrite UB. unfold page_size.
    apply (objs_clear_e_sound rho G24e Ce PGB 4096 HF2 CLe ltac:(lia)); [rewrite UB; left; lia | rewrite UB; intros y Hy; lia | | exact Ho].
    rewrite UB. intros e sz Hin y Hy. assert (Hy2 : 0x80015000 <= y) by lia.
    apply (blocks24_low rho HR H159 H160 H161 e sz Hin y ltac:(lia) (or_intror Hy2)).
  - intros X; exact X.
Qed.

Lemma clear24Aa : objs_clear_e G24 C22Aa = true /\ objs_clear_e G24e C22Ae = true.
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C22Aa_facts_eq : ss_facts C22Aa = ss_facts (ax_S EGA) /\ ax_setS EGA C22Aa = mkAX C22Aa [] (SLit SHB).
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma shapeA : forall (J : jpredA) rho tp w, SPA segsA J EGA rho tp w -> SPA segsA J (mkAX C22Aa [] (SLit SHB)) rho tp w.
Proof.
  clear. intros J rho tp w Hsp. destruct C22Aa_facts_eq as [_ E]. rewrite <- E.
  exact (SPA_split_chain segsA J rho splits22 EGA C22Aa tp w split22A_ok Hsp).
Qed.

Lemma payA : forall rho ms md, rhoOK rho -> rw rho 159%positive = b12 -> rw rho 160%positive = b13 -> rw rho 161%positive = b14 ->
  SPA segsA (KxA (m24 b12 b13 b14) B24) (mkAX C22Aa [] (SLit SHB)) rho (b13 :: TP18 rho) ([], mkCfg ms md) ->
  SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22A rho (PGB :: PGA :: b13 :: TP18 rho) ([], mkCfg ms md).
Proof.
  intros rho ms md HR H159 H160 H161 Hsp. destruct C22Ae_facts as (EQe & SBe & EQg & SBg). destruct clear24Aa as [CLa CLe]. unfold C22A.
  exact (pay_pages C22Aa C22Ae C22Ag rho ms md HR H159 H160 H161 EQe SBe EQg SBg CLa CLe Hsp).
Qed.

Lemma callA : forall rho tp,
  triple segsA ok (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22A rho tp)
    (fun w => exists rho', agree_below 162%positive rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGAf rho' tp w).
Proof.
  clear - OKF. intros rho tp. apply triple_factsA. intros HFx. cbn [ax_S] in HFx.
  apply (call_pureA segsA ok C22A Pre_G2 Posts_G2 s22A R22A (m24 b12 b13 b14) (B24 + 8192) tp rho _ OKF ent22A chk22A).
  - intros J rho1 tp1 HokJ HstJ. exact (regglob2_sum ok J rho1 tp1 HokJ HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state]. rewrite IGA_eq.
    replace (ss_next (ax_S C22A)) with 162%positive in Hag by (symmetry; exact (proj1 (proj2 C22A_at))).
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply triple_refl].
    exists rho'. split; [exact Hag|]. rewrite <- IGAf_eq. apply SPA_refacts.
    + apply SPA_x_sub; [intros r []| exact Hw].
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros HF'. apply Forall_app. split; [exact HF'|]. apply (holds_all_agree 162%positive rho rho' _ C22A_facts_below Hag). exact HFx.
Qed.

Lemma ecallA : forall rho tp,
  etriple segsA (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22A rho tp)
    (fun w => exists rho', agree_below 162%positive rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGAf rho' tp w).
Proof.
  clear. intros rho tp. apply etriple_factsA. intros HFx. cbn [ax_S] in HFx.
  apply (ecall_pureA segsA C22A Pre_G2 Posts_G2 s22A R22A (m24 b12 b13 b14) (B24 + 8192) tp rho _ ent22A chk22A).
  - intros J rho1 tp1 HstJ. exact (regglob2_sum_ex J rho1 tp1 HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state]. rewrite IGA_eq.
    replace (ss_next (ax_S C22A)) with 162%positive in Hag by (symmetry; exact (proj1 (proj2 C22A_at))).
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply etriple_refl].
    exists rho'. split; [exact Hag|]. rewrite <- IGAf_eq. apply SPA_refacts.
    + apply SPA_x_sub; [intros r []| exact Hw].
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros HF'. apply Forall_app. split; [exact HF'|]. apply (holds_all_agree 162%positive rho rho' _ C22A_facts_below Hag). exact HFx.
Qed.

Definition NXA : positive := Eval vm_compute in ss_next (ax_S IGAf).
Lemma runMA_safe : forall rho tp,
  triple segsA ok (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGAf rho tp)
    (fun w => exists rho', agree_below NXA rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) MAINA rho' tp w).
Proof.
  clear - OKF. intros rho tp. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) |].
  apply triple1_triple. replace NXA with (ss_next (ax_S IGAf)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  eapply sym_run_soundA; [exact runMA | apply OKFx | reflexivity | apply stableA_KxA].
Qed.
Lemma erunMA : forall rho tp,
  etriple segsA (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGAf rho tp)
    (fun w => exists rho', agree_below NXA rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) MAINA rho' tp w).
Proof.
  clear. intros rho tp. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) |].
  replace NXA with (ss_next (ax_S IGAf)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact runMA].
Qed.

Lemma clear24Ba : objs_clear_e G24 C22Ba = true /\ objs_clear_e G24e C22Be = true.
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C22Ba_facts_eq : ss_facts C22Ba = ss_facts (ax_S EGB) /\ ax_setS EGB C22Ba = mkAX C22Ba [] (SLit SHB).
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma shapeB : forall (J : jpredA) rho tp w, SPA segsA J EGB rho tp w -> SPA segsA J (mkAX C22Ba [] (SLit SHB)) rho tp w.
Proof.
  clear. intros J rho tp w Hsp. destruct C22Ba_facts_eq as [_ E]. rewrite <- E.
  exact (SPA_split_chain segsA J rho splits22 EGB C22Ba tp w split22B_ok Hsp).
Qed.

Lemma payB : forall rho ms md, rhoOK rho -> rw rho 159%positive = b12 -> rw rho 160%positive = b13 -> rw rho 161%positive = b14 ->
  SPA segsA (KxA (m24 b12 b13 b14) B24) (mkAX C22Ba [] (SLit SHB)) rho (b13 :: TP18 rho) ([], mkCfg ms md) ->
  SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22B rho (PGB :: PGA :: b13 :: TP18 rho) ([], mkCfg ms md).
Proof.
  intros rho ms md HR H159 H160 H161 Hsp. destruct C22Be_facts as (EQe & SBe & EQg & SBg). destruct clear24Ba as [CLa CLe]. unfold C22B.
  exact (pay_pages C22Ba C22Be C22Bg rho ms md HR H159 H160 H161 EQe SBe EQg SBg CLa CLe Hsp).
Qed.

Lemma callB : forall rho tp,
  triple segsA ok (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22B rho tp)
    (fun w => exists rho', agree_below 162%positive rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGBf rho' tp w).
Proof.
  clear - OKF. intros rho tp. apply triple_factsA. intros HFx. cbn [ax_S] in HFx.
  apply (call_pureA segsA ok C22B Pre_G2 Posts_G2 s22B R22B (m24 b12 b13 b14) (B24 + 8192) tp rho _ OKF ent22B chk22B).
  - intros J rho1 tp1 HokJ HstJ. exact (regglob2_sum ok J rho1 tp1 HokJ HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state]. rewrite IGB_eq.
    replace (ss_next (ax_S C22B)) with 162%positive in Hag by (symmetry; exact (proj1 (proj2 C22B_at))).
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply triple_refl].
    exists rho'. split; [exact Hag|]. rewrite <- IGBf_eq. apply SPA_refacts.
    + apply SPA_x_sub; [intros r []| exact Hw].
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros HF'. apply Forall_app. split; [exact HF'|]. apply (holds_all_agree 162%positive rho rho' _ C22B_facts_below Hag). exact HFx.
Qed.

Lemma ecallB : forall rho tp,
  etriple segsA (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22B rho tp)
    (fun w => exists rho', agree_below 162%positive rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGBf rho' tp w).
Proof.
  clear. intros rho tp. apply etriple_factsA. intros HFx. cbn [ax_S] in HFx.
  apply (ecall_pureA segsA C22B Pre_G2 Posts_G2 s22B R22B (m24 b12 b13 b14) (B24 + 8192) tp rho _ ent22B chk22B).
  - intros J rho1 tp1 HstJ. exact (regglob2_sum_ex J rho1 tp1 HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state]. rewrite IGB_eq.
    replace (ss_next (ax_S C22B)) with 162%positive in Hag by (symmetry; exact (proj1 (proj2 C22B_at))).
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply etriple_refl].
    exists rho'. split; [exact Hag|]. rewrite <- IGBf_eq. apply SPA_refacts.
    + apply SPA_x_sub; [intros r []| exact Hw].
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros HF'. apply Forall_app. split; [exact HF'|]. apply (holds_all_agree 162%positive rho rho' _ C22B_facts_below Hag). exact HFx.
Qed.

Definition NXB : positive := Eval vm_compute in ss_next (ax_S IGBf).
Lemma runMB_safe : forall rho tp,
  triple segsA ok (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGBf rho tp)
    (fun w => exists rho', agree_below NXB rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) MAINB rho' tp w).
Proof.
  clear - OKF. intros rho tp. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) |].
  apply triple1_triple. replace NXB with (ss_next (ax_S IGBf)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  eapply sym_run_soundA; [exact runMB | apply OKFx | reflexivity | apply stableA_KxA].
Qed.
Lemma erunMB : forall rho tp,
  etriple segsA (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) IGBf rho tp)
    (fun w => exists rho', agree_below NXB rho rho' /\ SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) MAINB rho' tp w).
Proof.
  clear. intros rho tp. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) |].
  replace NXB with (ss_next (ax_S IGBf)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact runMB].
Qed.
End S24.
End S23.
End S22.

Definition MAIN_of (v : bool) : axst := pick v MAINA MAINB.
Definition TPmain (b13 : word) (rho : valuation) : list word := PGB :: PGA :: b13 :: TP18 rho.
Definition Bmain : Z := B24 + 8192.

Definition Post22 (rho : valuation) : assn := fun w =>
  exists (v : bool) (b12 b13 b14 : word) (rho' : valuation),
    mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) b12
    /\ mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) b13
    /\ mmap_place_ok_none (Z_to_bv 64 0) (m23a b12 b13) (Z_to_bv 64 4096) b14
    /\ (forall i, (i < 159)%positive -> rw rho' i = rw rho i) /\ rw rho' 159%positive = b12 /\ rw rho' 160%positive = b13 /\ rw rho' 161%positive = b14
    /\ (forall l, rl rho' l = rl rho l)
    /\ (forall a : word, ~ (bv_unsigned b13 <= bv_unsigned a < bv_unsigned b13 + 8388608) -> rm rho' a = rm rho a)
    /\ SPA segsA (KxA (m24 b12 b13 b14) Bmain) (MAIN_of v) rho' (TPmain b13 rho) w.

Theorem seg22 : forall rho, rhoOK rho -> triple segsA ok (SPA segsA (KxA mo B18) K18 rho (TP18 rho)) (Post22 rho).
Proof.
  intros rho HR.
  pose proof (TP18_facts rho HR) as Htp.

  eapply triple_seq; [apply run22_safe|].
  apply triple_ex; intros v. apply triple_ex; intros rho1. apply triple_pure; intros Hag1.
  pose proof Hag1 as (V1 & L1 & M1).
  assert (HR1 : rhoOK rho1) by (apply (rhoOK_agree 159%positive rho); [lia | exact HR | intros i Hi; symmetry; apply V1; exact Hi]).

  eapply triple_seq; [apply (node22 v rho1 _ HR1)|].
  apply triple_ex; intros b12. apply triple_pure; intros HPL12.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho2. apply triple_pure; intros Hag2. pose proof Hag2 as (V2 & L2 & M2).
  assert (HR2 : rhoOK rho2).
  { apply (rhoOK_agree 159%positive rho1); [lia | exact HR1 | intros i Hi; rewrite <- (V2 i) by lia; apply rho_set_rw_other; lia]. }
  assert (H159 : rw rho2 159%positive = b12) by (rewrite <- (V2 159%positive) by lia; apply rho_set_rw_at).

  eapply triple_seq; [apply (node23 b12 HPL12 v rho2 _ HR2 H159 Htp)|].
  apply triple_ex; intros b13. apply triple_pure; intros HPL13.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho3. apply triple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & M3).
  assert (HR3 : rhoOK rho3).
  { apply (rhoOK_agree 160%positive rho2); [lia | exact HR2 | intros i Hi; rewrite <- (V3 i) by lia; unfold rho23; rewrite rho_set_rw_other by lia; reflexivity]. }
  assert (H159c : rw rho3 159%positive = b12) by (rewrite <- (V3 159%positive) by lia; unfold rho23; rewrite rho_set_rw_other by lia; cbn; exact H159).
  assert (H160 : rw rho3 160%positive = b13) by (rewrite <- (V3 160%positive) by lia; unfold rho23; apply rho_set_rw_at).

  eapply triple_seq; [apply (node24 b12 HPL12 b13 HPL13 v rho3 _ HR3 H159c H160)|].
  apply triple_ex; intros b14. apply triple_pure; intros HPL14.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho4. apply triple_pure; intros Hag4. pose proof Hag4 as (V4 & L4 & M4).
  assert (HR4 : rhoOK rho4).
  { apply (rhoOK_agree 161%positive rho3); [lia | exact HR3 | intros i Hi; rewrite <- (V4 i) by lia; apply rho_set_rw_other; lia]. }
  assert (H159d : rw rho4 159%positive = b12) by (rewrite <- (V4 159%positive) by lia; rewrite rho_set_rw_other by lia; exact H159c).
  assert (H160d : rw rho4 160%positive = b13) by (rewrite <- (V4 160%positive) by lia; rewrite rho_set_rw_other by lia; exact H160).
  assert (H161d : rw rho4 161%positive = b14) by (rewrite <- (V4 161%positive) by lia; apply rho_set_rw_at).
  assert (RW4 : forall i, (i < 159)%positive -> rw rho4 i = rw rho i).
  { intros i Hi. rewrite <- (V4 i) by lia. rewrite rho_set_rw_other by lia. rewrite <- (V3 i) by lia. unfold rho23. rewrite rho_set_rw_other by lia. cbn [rw set_rm].
    rewrite <- (V2 i) by lia. rewrite rho_set_rw_other by lia. symmetry. apply V1. lia. }
  assert (RL4 : forall l, rl rho4 l = rl rho l).
  { intros l. rewrite <- L4, rho_set_rw_rl, <- L3. unfold rho23. rewrite rho_set_rw_rl. cbn [rl set_rm]. rewrite <- L2, rho_set_rw_rl. symmetry. apply L1. }
  assert (T4 : TP18 rho4 = TP18 rho) by (apply (Start7.TP18_ext x); [intros i Hi; apply RW4; lia | exact RL4]).
  rewrite <- T4. unfold TPmain.

  assert (POST : forall rho6 (w : world), (exists n, (162 <= n)%positive /\ agree_below n rho4 rho6) ->
            SPA segsA (KxA (m24 b12 b13 b14) Bmain) (MAIN_of v) rho6 (PGB :: PGA :: b13 :: TP18 rho4) w -> Post22 rho w).
  { intros rho6 w (n & Hn & (V6 & L6 & M6)) Hsp. exists v, b12, b13, b14, rho6.
    split; [exact HPL12|]. split; [exact HPL13|]. split; [exact HPL14|].
    split; [intros i Hi; rewrite <- (V6 i) by lia; apply RW4; exact Hi|].
    split; [rewrite <- (V6 159%positive) by lia; exact H159d|]. split; [rewrite <- (V6 160%positive) by lia; exact H160d|].
    split; [rewrite <- (V6 161%positive) by lia; exact H161d|].
    split; [intros l; rewrite <- L6; apply RL4|].
    split; [|unfold TPmain; rewrite <- T4; exact Hsp].
    intros a Ha. rewrite <- M6, <- M4, rho_set_rw_rm, <- M3, (rm_rho23 rho2 b13 a Ha), <- M2, rho_set_rw_rm. symmetry. apply M1. }
  destruct v.
  - eapply (@triple_conseq segsA ok (fun w => w_tr w = [] /\ SPA segsA (KxA (m24 b12 b13 b14) B24) (mkAX C22Aa [] (SLit SHB)) rho4 (b13 :: TP18 rho4) w));
      [intros w Hw; split; [exact (proj1 (proj2 Hw)) | exact (shapeA _ _ _ _ Hw)] | intros w Hw; exact Hw |].
    eapply (@triple_conseq segsA ok (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22A rho4 (PGB :: PGA :: b13 :: TP18 rho4)));
      [intros [tr [ms md]] [Htr Hw]; cbn in Htr; subst tr; exact (payA b12 HPL12 b13 HPL13 b14 HPL14 rho4 ms md HR4 H159d H160d H161d Hw) | intros w Hw; exact Hw |].
    eapply triple_seq; [apply (callA b12 b13 b14)|].
    apply triple_ex; intros rho5. apply triple_pure; intros Hag5.
    eapply triple_conseq; [intros w Hw; exact Hw | | apply (runMA_safe b12 b13 b14)].
    intros w (rho6 & Hag6 & Hsp). apply (POST rho6 w); [|exact Hsp].
    exists 162%positive. split; [lia|]. eapply agree_below_trans; [exact Hag5|]. eapply agree_below_le; [|exact Hag6]. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - eapply (@triple_conseq segsA ok (fun w => w_tr w = [] /\ SPA segsA (KxA (m24 b12 b13 b14) B24) (mkAX C22Ba [] (SLit SHB)) rho4 (b13 :: TP18 rho4) w));
      [intros w Hw; split; [exact (proj1 (proj2 Hw)) | exact (shapeB _ _ _ _ Hw)] | intros w Hw; exact Hw |].
    eapply (@triple_conseq segsA ok (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22B rho4 (PGB :: PGA :: b13 :: TP18 rho4)));
      [intros [tr [ms md]] [Htr Hw]; cbn in Htr; subst tr; exact (payB b12 HPL12 b13 HPL13 b14 HPL14 rho4 ms md HR4 H159d H160d H161d Hw) | intros w Hw; exact Hw |].
    eapply triple_seq; [apply (callB b12 b13 b14)|].
    apply triple_ex; intros rho5. apply triple_pure; intros Hag5.
    eapply triple_conseq; [intros w Hw; exact Hw | | apply (runMB_safe b12 b13 b14)].
    intros w (rho6 & Hag6 & Hsp). apply (POST rho6 w); [|exact Hsp].
    exists 162%positive. split; [lia|]. eapply agree_below_trans; [exact Hag5|]. eapply agree_below_le; [|exact Hag6]. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Hypothesis Hwit23 : forall b12, mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) b12 ->
  exists a, mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) a.
Hypothesis Hwit24 : forall b12 b13, mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) b12 -> mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) b13 ->
  exists a, mmap_place_ok_none (Z_to_bv 64 0) (m23a b12 b13) (Z_to_bv 64 4096) a.

Theorem eseg22 : forall rho, rhoOK rho -> etriple segsA (SPA segsA (KxA mo B18) K18 rho (TP18 rho)) (Post22 rho).
Proof.
  intros rho HR.
  pose proof (TP18_facts rho HR) as Htp.
  eapply etriple_seq; [apply erun22|].
  apply etriple_ex; intros v. apply etriple_ex; intros rho1. apply etriple_pure; intros Hag1.
  pose proof Hag1 as (V1 & L1 & M1).
  assert (HR1 : rhoOK rho1) by (apply (rhoOK_agree 159%positive rho); [lia | exact HR | intros i Hi; symmetry; apply V1; exact Hi]).
  eapply etriple_seq; [apply (enode22 v rho1 _ HR1)|].
  apply etriple_ex; intros b12. apply etriple_pure; intros HPL12.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho2. apply etriple_pure; intros Hag2. pose proof Hag2 as (V2 & L2 & M2).
  assert (HR2 : rhoOK rho2).
  { apply (rhoOK_agree 159%positive rho1); [lia | exact HR1 | intros i Hi; rewrite <- (V2 i) by lia; apply rho_set_rw_other; lia]. }
  assert (H159 : rw rho2 159%positive = b12) by (rewrite <- (V2 159%positive) by lia; apply rho_set_rw_at).
  eapply etriple_seq; [apply (enode23 b12 HPL12 (Hwit23 b12 HPL12) v rho2 _ HR2 H159 Htp)|].
  apply etriple_ex; intros b13. apply etriple_pure; intros HPL13.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho3. apply etriple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & M3).
  assert (HR3 : rhoOK rho3).
  { apply (rhoOK_agree 160%positive rho2); [lia | exact HR2 | intros i Hi; rewrite <- (V3 i) by lia; unfold rho23; rewrite rho_set_rw_other by lia; reflexivity]. }
  assert (H159c : rw rho3 159%positive = b12) by (rewrite <- (V3 159%positive) by lia; unfold rho23; rewrite rho_set_rw_other by lia; cbn; exact H159).
  assert (H160 : rw rho3 160%positive = b13) by (rewrite <- (V3 160%positive) by lia; unfold rho23; apply rho_set_rw_at).
  eapply etriple_seq; [apply (enode24 b12 HPL12 b13 HPL13 (Hwit24 b12 b13 HPL12 HPL13) v rho3 _ HR3 H159c H160)|].
  apply etriple_ex; intros b14. apply etriple_pure; intros HPL14.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho4. apply etriple_pure; intros Hag4. pose proof Hag4 as (V4 & L4 & M4).
  assert (HR4 : rhoOK rho4).
  { apply (rhoOK_agree 161%positive rho3); [lia | exact HR3 | intros i Hi; rewrite <- (V4 i) by lia; apply rho_set_rw_other; lia]. }
  assert (H159d : rw rho4 159%positive = b12) by (rewrite <- (V4 159%positive) by lia; rewrite rho_set_rw_other by lia; exact H159c).
  assert (H160d : rw rho4 160%positive = b13) by (rewrite <- (V4 160%positive) by lia; rewrite rho_set_rw_other by lia; exact H160).
  assert (H161d : rw rho4 161%positive = b14) by (rewrite <- (V4 161%positive) by lia; apply rho_set_rw_at).
  assert (RW4 : forall i, (i < 159)%positive -> rw rho4 i = rw rho i).
  { intros i Hi. rewrite <- (V4 i) by lia. rewrite rho_set_rw_other by lia. rewrite <- (V3 i) by lia. unfold rho23. rewrite rho_set_rw_other by lia. cbn [rw set_rm].
    rewrite <- (V2 i) by lia. rewrite rho_set_rw_other by lia. symmetry. apply V1. lia. }
  assert (RL4 : forall l, rl rho4 l = rl rho l).
  { intros l. rewrite <- L4, rho_set_rw_rl, <- L3. unfold rho23. rewrite rho_set_rw_rl. cbn [rl set_rm]. rewrite <- L2, rho_set_rw_rl. symmetry. apply L1. }
  assert (T4 : TP18 rho4 = TP18 rho) by (apply (Start7.TP18_ext x); [intros i Hi; apply RW4; lia | exact RL4]).
  rewrite <- T4. unfold TPmain.
  assert (POST : forall rho6 (w : world), (exists n, (162 <= n)%positive /\ agree_below n rho4 rho6) ->
            SPA segsA (KxA (m24 b12 b13 b14) Bmain) (MAIN_of v) rho6 (PGB :: PGA :: b13 :: TP18 rho4) w -> Post22 rho w).
  { intros rho6 w (n & Hn & (V6 & L6 & M6)) Hsp. exists v, b12, b13, b14, rho6.
    split; [exact HPL12|]. split; [exact HPL13|]. split; [exact HPL14|].
    split; [intros i Hi; rewrite <- (V6 i) by lia; apply RW4; exact Hi|].
    split; [rewrite <- (V6 159%positive) by lia; exact H159d|]. split; [rewrite <- (V6 160%positive) by lia; exact H160d|].
    split; [rewrite <- (V6 161%positive) by lia; exact H161d|].
    split; [intros l; rewrite <- L6; apply RL4|].
    split; [|unfold TPmain; rewrite <- T4; exact Hsp].
    intros a Ha. rewrite <- M6, <- M4, rho_set_rw_rm, <- M3, (rm_rho23 rho2 b13 a Ha), <- M2, rho_set_rw_rm. symmetry. apply M1. }
  destruct v.
  - eapply (@etriple_conseq segsA (fun w => w_tr w = [] /\ SPA segsA (KxA (m24 b12 b13 b14) B24) (mkAX C22Aa [] (SLit SHB)) rho4 (b13 :: TP18 rho4) w));
      [intros w Hw; split; [exact (proj1 (proj2 Hw)) | exact (shapeA _ _ _ _ Hw)] | intros w Hw; exact Hw |].
    eapply (@etriple_conseq segsA (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22A rho4 (PGB :: PGA :: b13 :: TP18 rho4)));
      [intros [tr [ms md]] [Htr Hw]; cbn in Htr; subst tr; exact (payA b12 HPL12 b13 HPL13 b14 HPL14 rho4 ms md HR4 H159d H160d H161d Hw) | intros w Hw; exact Hw |].
    eapply etriple_seq; [apply (ecallA b12 b13 b14)|].
    apply etriple_ex; intros rho5. apply etriple_pure; intros Hag5.
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply (erunMA b12 b13 b14)].
    intros w (rho6 & Hag6 & Hsp). apply (POST rho6 w); [|exact Hsp].
    exists 162%positive. split; [lia|]. eapply agree_below_trans; [exact Hag5|]. eapply agree_below_le; [|exact Hag6]. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - eapply (@etriple_conseq segsA (fun w => w_tr w = [] /\ SPA segsA (KxA (m24 b12 b13 b14) B24) (mkAX C22Ba [] (SLit SHB)) rho4 (b13 :: TP18 rho4) w));
      [intros w Hw; split; [exact (proj1 (proj2 Hw)) | exact (shapeB _ _ _ _ Hw)] | intros w Hw; exact Hw |].
    eapply (@etriple_conseq segsA (SPA segsA (KxA (m24 b12 b13 b14) (B24 + 8192)) C22B rho4 (PGB :: PGA :: b13 :: TP18 rho4)));
      [intros [tr [ms md]] [Htr Hw]; cbn in Htr; subst tr; exact (payB b12 HPL12 b13 HPL13 b14 HPL14 rho4 ms md HR4 H159d H160d H161d Hw) | intros w Hw; exact Hw |].
    eapply etriple_seq; [apply (ecallB b12 b13 b14)|].
    apply etriple_ex; intros rho5. apply etriple_pure; intros Hag5.
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply (erunMB b12 b13 b14)].
    intros w (rho6 & Hag6 & Hsp). apply (POST rho6 w); [|exact Hsp].
    exists 162%positive. split; [lia|]. eapply agree_below_trans; [exact Hag5|]. eapply agree_below_le; [|exact Hag6]. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Theorem MI_main : forall b12 b13 b14,
  mmap_place_ok_none (Z_to_bv 64 0) mo (Z_to_bv 64 1048576) b12 ->
  mmap_place_ok_none (Z_to_bv 64 0) (m22 b12) (Z_to_bv 64 8388608) b13 ->
  mmap_place_ok_none (Z_to_bv 64 0) (m23a b12 b13) (Z_to_bv 64 4096) b14 ->
  minv8 (L24 b12 b13 b14) (vm_limit (m_vmmaps m)) (vm_init_sp (m_vmmaps m)) Q18 (m24 b12 b13 b14)
  /\ (0x646000 <= bv_unsigned b12 /\ (bv_unsigned b12 + 1048576 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b12) /\ bv_unsigned b12 mod 4096 = 0 /\ bv_unsigned b12 + 1048576 <= TOPz)
  /\ (0x646000 <= bv_unsigned b13 /\ (bv_unsigned b13 + 8388608 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b13) /\ bv_unsigned b13 mod 4096 = 0 /\ bv_unsigned b13 + 8388608 <= TOPz)
  /\ (0x1000 <= bv_unsigned b14 /\ (bv_unsigned b14 + 4096 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b14) /\ bv_unsigned b14 mod 4096 = 0 /\ bv_unsigned b14 + 4096 <= TOPz).
Proof.
  clear - HMI Hxtop. intros b12 b13 b14 HPL12 HPL13 HPL14.
  pose proof (MI22 b12 HPL12) as (_ & F12). pose proof (MI23 b12 HPL12 b13 HPL13) as (_ & F13). pose proof (MI24 b12 HPL12 b13 HPL13 b14 HPL14) as (MI & F14).
  split; [exact MI|]. split; [exact F12|]. split; [exact F13 | exact F14].
Qed.

End Seg8.
End Start8.

(* [comment removed for export] *)
Module DrvRe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "sprop"; "eval"; "SLit"; "cell"; "ss_next"; "sobj"; "holds"; "sprop_eqb"; "obj_range"; "sstate"; "SVar"; "rm"; "ss_facts"; "obj_hi_of"; "obj_holds"; "obj_lo_of"; "SPBranch"; "SPUle"; "c_off"; "ss_objs"; "c_val"; "c_width"; "soff"; "DUnknown"; "SAlu"; "mkObj"; "SPNot"; "agree_below"; "reg_sv"; "ss_lenient"; "ss_pc"; "SExt"; "mkSS"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nil"; "true"; "bool"; "length"; "Some"; "option"; "app"; "nat"; "cons"; "pair"; "fst"; "snd"; "S"; "None"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "proj1"; "proj2"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "mul"; "sub"; "modulo"; "to_nat"; "div"; "min"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.DrvRe.RE"; "JR"; "KcR"; "KcC"; "KcG"; "lit_cells"; "MDT"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "m_fs"; "WriteEv"; "fd_lookup"; "ExitEv"; "m_fds"; "FdFile"; "FdChannel"; "VmState"; "with_fds"; "FdDir"; "fd_insert"; "fd_remove"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "jpredA"; "LQA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "w_tr"; "w_cfg"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts"; "nd_R"; "nd_Z"; "node_okb"; "O_rdsW"; "O_rdsZL"; "N_rd"; "O_rdsZ"; "bk_facts"; "bkz_facts"; "len1"; "qz_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "ax_X"; "la_state"; "ax_base"; "sym_runA"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR"; "cap"; "SHR"; "BXk"; "P0RD1"; "U"; "SHRZ"; "P0R1"; "K0"; "P0G"; "P0RD0"; "P0R0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "JA"; "nd_below"; "nd_am"; "nd_tv"; "JAi"; "nd_bd"; "nd_fr"; "ANone"; "NDA"; "bxa"; "am_eqb"; "am_subst"; "apot"; "fr_sub_eqb"; "PTrue"; "amode"; "keptFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "AE_A"; "V_TOP"; "with_vm"; "alloc_contractsA_ex"; "band_free"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "KU"; "bitem"; "bx2"; "bd_subst"; "bd_wpos"; "bsumK"; "bsumV"; "bud_le"; "bxN"; "bxS"; "bxt"; "uval"; "BIc"; "BUD"; "bd_nn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "EVS"; "Kw"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read"; "E_ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cls_keptA"; "cls_kept_freeA"; "@Stdlib.Lists.List"; "existsb"; "In"; "Forall2"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.DrvRe.RE.FirstRead"; "res0"; "J0s"; "BS0"; "J1h"; "J1k";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "RS"; "R1c"; "vWant"; "G_cut"; "Lref"; "O_rdsL"; "S0f"; "rds_cellsL"; "Lov1"; "Lsh1"; "Ltr"; "X_R"; "CUTS_R"; "E_m"; "Hc0"; "Hc1"; "HcZ"; "Lsh0"; "LshZ"; "O_rdsC"; "Q1"; "QZh"; "QZk"; "R0c"; "RD0"; "RD1"; "objs37"; "vRes1"; "O_dstC"; "O_dstL"; "O_dstZ"; "O_rdsP"; "XF_q"; "clen_x"; "rdsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "SH0"; "BX0"; "KV_T"; "KP_T"; "HKVrng_T"; "JT"; "CST_drv"; "HCSTKV_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "hdr_word"; "vB"; "ATOPHI"; "clen_of"; "vLen"; "K_T"; "S_T"; "nd_T"; "vCap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lcarve"; "JAK"; "lc_obj"; "JA_carve"; "JA_uncarve"; "carve_okb"; "pure_callJ_ex"; "tv_bandfree"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cells_ok"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.DrvRe.RE.ReadStep1"; "res1"; "J0rd"; "J1rd"; "BS1"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "P0Z"; "S_R0"; "nd_R0"; "CAP0"; "CST_drv2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "rho_absorb"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA"; "rbA_bs"; "rbA_md'"; "rkA_rho'"; "rhA_rho'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "MAX_INPUT"; "msg_refused"; "msg_overrun"; "msg_short"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "fw_msgs"; "MSGB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.DrvRe.RE.ReadStep0"; "J0r0"; "J1r0"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "BC_NE"; "instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "Ecall"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_tfacts"; "ndT"; "nd_X"; "tailF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.DrvRe.RE.KV"; "HKV_R"; "HKP_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "tnz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp"; "EVSr"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_dstates"; "D_rde";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "mergeA"; "splitA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.DrvRe.RE.RDir"; "J0d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "hdr_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.ErrnoA"; "errno_blind"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "malloc_contractA_strong_ex"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform SysRead HasZero.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS IfaceEx GlueM InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB SysStepA SysA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.ErrnoA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysStepA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_read_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Icpt_memcpy_hdr_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memcpyAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Icpt_memcpy_rs_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvErrno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR_facts DrvR_tfacts DrvR_dstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvSiteEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.DrvJRe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvRGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_tfacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_dstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma call_checkPA_2b : ltac2:(tb__ "0|1|
S80S80S128S2dSbA1S80S80S3eS31S14fR6R5R4R3S37S80R2S37S80R1S2fS80A1M0A3A3A5S30A3S3eS31S14fR7R6R5R4S37S80R2G0A3A5S30A3F_;FB;FA;FR;Fs;FPre;FC;").
Proof.
  intros C Pre s R A B H. unfold call_checkPA, call_checkP in *. cbn [map forallb] in *.
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H1d]. apply andb_prop in H1d as [Pa Pb].
  apply andb_prop in H2 as [Xa Xb].
  rewrite H1, Pb, Xb. reflexivity.
Qed.

Section RE.
Variable AInv : ltac2:(tb__ "0|0|
Sc7S3S2dS46Q40A1A1S5dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S115VCST;R1A2S3fS4aZ0R2A2S4cR2S113A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S115VXGL;R1A2S3fS4aZ0R2A2S4cR2S113A2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HLF : law_fds_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S0S115SfdR1A2S115VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis HCSTdrv2 : ltac2:(tb__ "0|0|
S0S115S126R1A2S115VCST;R2A2F_;Fz;").
Hypothesis ACX : ltac2:(tb__ "0|0|
SadS45SaaVAInv;VCST;VXGL;A5").
Hypothesis MSX : ltac2:(tb__ "0|0|
S16bS45SaaVAInv;VCST;VXGL;A5").

Variable Q : world -> Prop.

Variable F : list byte.
Variable p3 : list byte.
Variable T0 : list event.
Variable FDS : ltac2:(tb__ "0|0|
S0S2dS2eS46Q40A1S5eA2A1F_;").
Variable FDC : list (word * FdEntry).
Variable MDX : Model -> Prop.
Hypothesis HFDS1 : ltac2:(tb__ "0|0|
S0S3eS34S5eA1S61VFDS;R1A1S121A2S33S5eS65S121A1A2A3Foff;").
Hypothesis HFDS2 : ltac2:(tb__ "0|0|
S0S3eS34S5eA1S61VFDS;R1A1Sc2A2S33S5eS65Sc2A1A2A3Foff;").
Hypothesis HFDS3 : ltac2:(tb__ "0|1|
S0S3eS34S5eA1S61VFDS;R1A1S48Q40M0Z3A2A2S33S5eS64Vp3;S48G0R1A2A2A2A3Foff;").
Hypothesis HFDSstep : ltac2:(tb__ "0|2|
S0S0S4aZ0R2A2M0G0S4cS4bR4R3A2S4eZ2Z40A2A2S3eS2dS2eS46Q40M1A1S5eA2A1S69VFDS;R5A1S48G1Z3A2S64Vp3;S49G1S48G1R5A2S48G1R4A2A3A2A3VFDS;S4bR5R4A2A1A3F_;F_;F_;Fn;Foff;").
Hypothesis HFDC : ltac2:(tb__ "0|1|
S0S3eS2dS2eS46Q40M0A1S5eA2A1S6aVFDS;R1A1S48G0Z3A2A2VFDC;A3Foff;").
Hypothesis HFDC1 : ltac2:(tb__ "0|0|
S3eS34S5eA1S61VFDC;S121A2S33S5eS65S121A1A2A3").
Hypothesis HFDC2 : ltac2:(tb__ "0|0|
S3eS34S5eA1S61VFDC;Sc2A2S33S5eS65Sc2A1A2A3").
Hypothesis HMDXvm : ltac2:(tb__ "0|0|
S5dS66VMDX;R2A1VMDX;SacR2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDXfds : ltac2:(tb__ "0|0|
S5dS2dS2eS46Q40A1S5eA2A1VMDX;R2A1VMDX;S67R2R3A2A1F_;Ff;Fmd;").
Hypothesis HMDXfs : ltac2:(tb__ "0|1|
S5dVMDX;R1A1S3eS34S2dS46Q8A1A1M0A1S120S5fR2A1Vp3;A2S33G0VF;A2A3F_;Fmd;").

Variable PA : AA -> Prop.
Hypothesis HPAm : ltac2:(tb__ "0|0|
Sc7Sc7S0S4aZfc01R1A2VPA;R4A1Sc8R5R4R3A3VPA;R5A1F_;F_;F_;Fn;FA';FA;").
Hypothesis HPAf : ltac2:(tb__ "0|0|
S4aZ10000S4dS32S46Q8A1VF;A2A1A2Sc7Sc7VPA;R2A1Sc9R3R2A2VPA;R3A1F_;F_;FA';FA;F_;").

Definition KcG (fds : list (word * FdEntry)) (evs : list event) : KcA := ltac2:(tb__ "0|1|
S2dS5cA1M0S5dS3fS3eG0R2S35S5cVT0;Vevs;A3A3S3fS3eS2dS2eS46Q40A1S5eA2A1S63R1A1Vfds;A3VMDX;R1A1A2A2Lmd;Ltr;").
Definition KcR (off : Z) : KcA := KcG (FDS off) [].
Definition KcC : KcA := KcG FDC [].

Lemma m_fds_with_vm : ltac2:(tb__ "0|0|
S66S5dS3eS2dS2eS46Q40A1S5eA2A1S63SacR2R1A2A1S63R1A1A3Fmd;Fv;").
Proof. intros v md. destruct md; reflexivity. Qed.
Lemma KcG_ok : ltac2:(tb__ "0|0|
S2dS2eS46Q40A1S5eA2A1S2dS5cA1Sa9S59R2R1A2A1Fevs;Ffds;").
Proof. intros fds evs tr md v (H1 & H2 & H3). split; [exact H1|]. split; [rewrite m_fds_with_vm; exact H2 | apply HMDXvm; exact H3]. Qed.

Definition JR (Kc : KcA) (rho0 : valuation) (P0 : valuation -> Prop) (k : Z) (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S97VAInv;VCST;VXGL;S8aVKc;Vrho0;VP0;S2fS2eS0S0A2M0A1S2fS2eG0S0A2A1S8dVk;A1VPA;Vnd;Ac").

Lemma JR_Kc : ltac2:(tb__ "0|0|
Sa8S3S3OF_;S0S96S3S2dS46Q40A1A1S2dS5cA1S5dS56R9R8R7R6R5R4R3R2R1A9RaR3R2A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FP0;Frho0;FKc;").
Proof. intros Kc rho0 P0 k nd rho tp tr md (Ai & kc & _ & H & _). exact H. Qed.
Lemma JR_P0 : ltac2:(tb__ "0|0|
Sa8S3S3OF_;S0S96S3S2dS46Q40A1A1S2dS5cA1S5dS56R9R8R7R6R5R4R3R2R1A9S3fR8R9A1S12cS8aR9R5A3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FP0;Frho0;FKc;").
Proof. intros Kc rho0 P0 k nd rho tp tr md (Ai & kc & Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. Qed.
Lemma U_agree : ltac2:(tb__ "0|0|
S3S3S1S12cS8aR3R2A3S11fR2S8aA2S3eS0S8fR4R3A2S8fR5R3A2A3F_;F_;Fv;Frho;Frho0;").
Proof. intros rho0 rho v [Hv _] Hlt. unfold U. rewrite (Hv v Hlt). reflexivity. Qed.

Lemma JR_stable : ltac2:(tb__ "0|0|
Sa8S3S3OF_;S0S96S1Sa9R6A1S4aZ0R4A2S11eS8aR3A2S3eS31S98R4R5A2S30A3S6cS45R5S56RaR9R8R7R6A5A3F_;F_;F_;F_;Fn;Fnd;Fk;FP0;Frho0;FKc;").
Proof. intros Kc rho0 P0 k nd n HK Hk Hn Hb. apply (stableA_JA segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA HK ALA n nd Hn Hb). Qed.

Lemma JR_blind : ltac2:(tb__ "0|0|
Sa8S3S3OF_;S0S1S96S3eS31S98R2R1A2S30A3S169S56R7R6R5R4R2A5A1F_;Fnd;Fn;Fk;FP0;Frho0;FKc;").
Proof. intros Kc rho0 P0 k n nd Hb. unfold JR. exact (JA_errno_blind segs AInv CST XGL ALA HCST (fun a Ha => HCSTdrv a (errno_in_CST_drv a Ha)) NF Kc rho0 P0 [] [] (BXk k) PA n nd Hb). Qed.

Lemma JR_run : ltac2:(tb__ "0|2|
S2dS2eS46Q40A1M0S5eA2A1S2dS5cA1S3S3OF_;S0S96S36S2dS0A1S80S2dS82A1M1S3S2dG0A1S71OF_;S4aZ0R9A2S3eS34G1A1S87S45R8R7R6S30A5S33G1R5A2A3S3eS31S23S81R7A1A1S3dA3S3eS31S11dS8aSaS81R8A1A1A2S30A3S3eS31S98SaS81R9A1A1RcA2S30A3S82S3ScbS82R2RbA3S21SaS81RdA1A1RbR2A3S70S45S6bS45S56S59R16R15A2R14R13R12R11A5S85R4A1R3RbA5RaA3F_;F_;Frho';FL;S70S45S6bS45S56S59R13R12A2R11R10RfReA5RbR9R8A5R7A3F_;F_;F_;F_;F_;F_;FQ';Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;Fk;FP0;Frho0;Fevs;Ffds;").
Proof.
  intros fds evs rho0 P0 k nd fuel cuts A leaves rho tp Q' Hk Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  eapply (erunA_tr segs fuel cuts A leaves _ rho tp Q' Hrun Hlen (JR_stable _ rho0 P0 k nd _ (KcG_ok fds evs) Hk Hnf Hnb) H).
Qed.

Lemma JR_entails : ltac2:(tb__ "0|0|
Sa8S3S3OF_;S0S80S80S128S96S96S3S2dS46Q40A1A1S71Sa9RcA1S4aZ0RaA2S3eS31S88RaR9R8A3S30A3S3eS31S12bR9S8aA2S30A3S3eS31S11dS8aSaS81RcA1A1A2S30A3S3eS31S98SaS81RdA1A1RaA2S30A3S3eS31S155RcS9aRbA1S9aRaA1A3S30A3S3eS31Sa4RdS9dRcA1S9dRbA1A3S30A3S3eS31SbaS12S81R10A1A1Sb6ReS9cRcA1A2S9cRdA1A3S30A3S3eS31Sa1Sa2RfS99RdA1A2S99ReA1A2S30A3S6bS45S56R16R15R14R13RfA5R12RdRcRbA6S6bS45S56R17R16R15R14RfA5R12S127ReR11A2RdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k L T s ndi ndj rho tp w HK Hk. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 [] [] (BXk k) PA HK).
Qed.

Lemma JR_reorigin : ltac2:(tb__ "0|6|
S2dS5cA1S5dOFx0;Fx;S3S3OF_;M0G0S0S80S80S128S96S96S3S2dS46Q40A1A1S71S3eS31S88R8R7R6A3S30A3S3eS5S12aR7P18M1A2S10G1A1A3S3eS5S12aR8SabA2S10SabA1A3S3eS31S11dS8aSaS81RbA1A1A2S30A3S3eS31S98SaS81RcA1A1R9A2S30A3S3eS31S155RbS9aRaA1S9aR9A1A3S30A3S3eS31Sa4RcS9dRbA1S9dRaA1A3S30A3S3eS31SbaS12S81RfA1A1Sb6RdS9cRbA1A2S9cRcA1A3S30A3S3eS31Sa1Sa2ReS99RcA1A2S99RdA1A2S30A3Sc7S0Sb0S6ScReA1S12S81R13A1A1A3R17R18A1S12cS8aR19R10A3Sa7VCST;VXGL;R1aS2fS2eS0S0A2M2A1M3S2fS2eG2S0A2A1M4S11R1aA1S11R11A1A7R1cS72R10A1S138S73R10A1A1A2S9bVAInv;VCST;VXGL;S8aR1dR1cR1bG3G4S8dR19A1VPA;R15R7R6R13R12S72R11A1S138S73R11A1A1A12R1bS127R14R17A2A1F_;F_;F_;F_;F_;F_;Fkc;FAi;S6bS45S56R17R16R15R13RfA5R12RdRcRbA6S6bS45S56R18S127ReR11A2M5R15R14RfA5R12G5RdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;Fk;FP0';FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 P0' k L T s ndi ndj rho tp w. apply (SPA_reorigin_JA AInv CST XGL ALA NF Kc [] [] (BXk k) PA ltac:(cbv; reflexivity) ltac:(cbv; reflexivity)).
Qed.

Lemma JAi_rebud : ltac2:(tb__ "0|9|
Sa8S3S3OF_;SbdSbdS96S2dSb4A1Sc7S0S3S2dS46Q40A1A1S2dS5cA1S5dS3eS2eS0S0A2M0S38S0S0SbcR9A1SbbR9A1A4S38S0S0SbcRaA1SbbRaA1A4A3S4aZ0M1S39S0S0Sb5RaA1A3A2S4aG1S3aS0S0Sb5RbA1A3A2S3eS31Sb7RaA1S30A3S0S0S0Sc0S9cRfA1Sa0Sb5R11A1M2Sa3S99RfA1RbA2RcA3R3R2R1RbA6S3fSc1RfRcA2S3fS4aS4bS4bR4Sb9RfRcA2A2S39S0S0Sa0G2Sa3S99R10A1RcA2M3RdA3M4A3A2S4bS4bR4Sb9S9cR10A1M5RcA2A2S39S0S0Sa0Sb5R12A1G3RdA3M6A3A2A2S4aS4bSb8RfRcA2S3aS0S0G4A3A2S4bSb8G5RcA2S3aS0S0G6A3A2A2A2A2F_;FKf;FKm;FV;S9bVAInv;VCST;VXGL;S8aR12R11R10S2fG0A1M7S2fS2eG0S0A2A1M8RfVPA;RdRbRaR9R8R7R6A12S9bVAInv;VCST;VXGL;S8aR13R12R11G7G8RfVPA;S9fS9aReA1S9dReA1RdS99ReA1A4RcRbRaR9R8R7A12F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fbd';Fndi;FBX';FBX;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 BX BX' ndi bd' Ai kc rho tp tr md HSN HB1 HB2 Hw HI HJ. injection HSN as HSx HNx.
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK|]. split; [exact HP0|]. split; [exact HXA|]. split; [|split; [exact HPA | split; [unfold capK in *; rewrite HSx; exact HCK | unfold capN in *; cbn [nd_tv]; rewrite HNx; exact HCN]]].
  cbn [nd_bd nd_am]. destruct (HI _ _ _ HBU) as (NN & LV & LK).
  destruct HBU as (A1 & A2 & A3 & A4 & A5 & Hwf & Hnn & B1 & B2).
  unfold BUD. unfold bxa in *. cbn [fst snd bx2] in *.
  pose proof (XA_kc_nonneg _ _ _ _ _ _ HXA) as Hkc.
  pose proof (apot_range (nd_am ndi) rho) as APR.
  split; [cbn; lia|]. split; [cbn; lia|].
  split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact Hw|]. split; [exact NN|]. lia.
Qed.

Section KV.
Variable rho0 : valuation.
Variable P0 : valuation -> Prop.
Variable k : Z.
Hypothesis HP0SH : ltac2:(tb__ "0|0|
S3VP0;R1A1Sf7R2A1F_;Fr;").
Lemma HKV_R : ltac2:(tb__ "0|1|
Sa8S96Sc7S0S3S2dS46Q40A1A1S2dS5cA1S5dS9bVAInv;VCST;VXGL;S8aR8Vrho0;VP0;S2fS2eS0S0A2M0A1S2fS2eG0S0A2A1S8dVk;A1VPA;R7R6R5R4R3R2R1A12S116S117S45S11R5A1A2Sf9A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc';").
Proof.
  intros Kc' nd Ai kc rho tp tr md (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
  unfold KV_T. apply Forall_app. split; [|apply Forall_app; split; [|exact (KVpp_ok AInv CST HLPP Ai rho tp md HM)]].
  - pose proof (law_rtc _ _ _ ALA Ai rho tp md HM) as HR.
    apply Forall_forall. intros c Hc. exact (proj1 (Forall_forall _ _) HR c (KVrtc_in _ c Hc)).
  - destruct (HP0SH _ HP0) as [HZ _]. destruct HK0 as [K1 _].
    assert (BY : forall a, 0x800c0998 <= a < 0x800c09a8 -> view segs (rm rho) a = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite view_in by lia. rewrite DrvJ.rd_of_high by lia.
      rewrite (K1 a ltac:(lia)).
      - exact (HZ a Ha).
      - right. split; [|rewrite (HZ a Ha); discriminate]. exists (8 * (a - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
        + left. right. left. split; [apply HCSTdrv; exists 0x644ca8, 0x450; split; [cbn; tauto | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
        + unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    unfold KVsh. repeat constructor; intros j Hj; cbn [c_addr c_w c_val] in Hj |- *;
      rewrite BY by lia; f_equal;
      do 8 (destruct j as [|j]; [reflexivity|]); lia.
Qed.
Lemma HKP_R : ltac2:(tb__ "0|3|
Sa8S96Sc7S0S3S2dS46Q40M0A1A1S2dS5cA1S5dS0S0S0S9bVAInv;VCST;VXGL;S8aRbVrho0;VP0;S2fS2eS0S0A2M1A1S2fS2eG1S0A2A1S8dVk;A1VPA;RaR9R8R7R6R5R4A12ScbG1S38S0S0R4R3A4SfaA3S3fS4aR5R3A2S4cR3R4A2A2S3fS3fS4aZ646000R4A2S4cR4S4eZ2Z40A2A2A2S44S3eS34S46Q8A1M2A1S11RaS48G0R4A2A2S3cG2A1A3A1A2F_;F_;F_;Fz;Fhi;Flo;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc';").
Proof.
  intros Kc' nd Ai kc rho tp tr md lo hi z (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _) Hin Hz.
  destruct (HP0SH _ HP0) as [_ HP]. destruct HK0 as [K1 _].
  unfold KP_T in Hin. cbn in Hin.
  assert (RNG : 0x7fffc570 <= z < 0x7fffc750 \/ 0x800158a8 <= z < 0x80015ba8).
  { destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
  split; [lia|]. rewrite (K1 z ltac:(lia)); [exact (HP z RNG)|].
  right. split; [|exact (HP z RNG)]. exists (8 * (z - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
  - left. right. left. split; [apply HCSTdrv; destruct RNG as [R|R]; [exists 0x22b80, 0xf00 | exists 0xec540, 0x1800]; (split; [cbn; tauto | unfold SHADOW_OFF; lia])
                             | unfold errno_addrA, ERRNO_A, SHADOW_OFF; destruct RNG; lia].
  - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma SHR_kept : ltac2:(tb__ "0|4|
Sa8S96Sc7S0S3S2dS46Q40M0A1A1S2dS5cA1S5dS3VP0;R1A1S8cR2A1F_;Fr;S9bVAInv;VCST;VXGL;S8aR9Vrho0;VP0;S2fS2eS0S0A2M1A1S2fS2eG1S0A2A1S8dVk;A1VPA;R8R7R6R5R4R3R2A12S0S90R1A1S3eS34S46Q8M2A1M3A1S11R8S48G0R2A2A2S33G3S48G2Z0A2A2A3F_;Fz;F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc';").
Proof.
  intros Kc' nd Ai kc rho tp tr md HP (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _) z Hz.
  destruct (HP _ HP0) as [_ HZ]. destruct HK0 as [K1 _].
  assert (R64 : 0 <= z < 2 ^ 64) by (unfold SHRZ, Sh, SHADOW_OFF in Hz; lia).
  rewrite (K1 z R64); [exact (HZ z Hz)|].
  right. split; [|intro HcN; pose proof (HZ z Hz) as HcE; congruence].
  exists (8 * (z - SHADOW_OFF)). split; [unfold SHRZ, Sh, SHADOW_OFF in Hz |- *; lia|]. split.
  - left. right. left. unfold SHRZ, Sh, SHADOW_OFF in Hz |- *. split; [|unfold errno_addrA, ERRNO_A; lia].
    destruct Hz as [R|[R|R]].
    + apply HCSTdrv. exists 0x21440, 0x80. split; [cbn; tauto | lia].
    + destruct (Z_lt_le_dec z (0x160c0 / 8 + 2147450880)) as [Rlo|Rhi].
      * apply HCSTdrv2. exists 0x16080, 0x40. split; [cbn; tauto | lia].
      * apply HCSTdrv. exists 0x160c0, 0x40. split; [cbn; tauto | lia].
    + apply HCSTdrv. exists 0x1a7c0, 0x80. split; [cbn; tauto | lia].
  - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.
Definition carveR : ltac2:(tb__ "0|4|
Sa8S96S80S3S2dS46Q40A1A1S71S2dS109A1S1S6bS45S10aVAInv;VCST;VXGL;S8aVrho0;VP0;S2fS2eS0S0A2M0A1M1S2fS2eG0S0A2A1M2S8dVk;A1M3VPA;R8R7AcR6R5R4R3A6S81R7A1SfS26S24R1A1S2aR1A1S29R1A1S28R1A1S2bR1A1S35SbS19R1A1SafS109SbS10bR4A4A3S12R1A1R3S23R1A1A9SfS3eS31S2cR1A1S30A3S3eS31S11dSaR3A1R5A2S30A3S3eS5S86RbA1S8S114A1A3S3eS31S10eS12R5A1S19R5A1S84RcA1Sf9SfaS9aRdA1R8A7S30A3S6bS45S10aVAInv;VCST;VXGL;S8aVrho0;VP0;G1G2G3VPA;RfReAcS83RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
S10cVAInv;VCST;VXGL;VALA;S8aVrho0;VP0;S2fS2eS0S0A2M0A1S2fS2eG0S0A2A1S8dVk;A1VPA;Sf9S14aSfbSfaS14bA10").
Definition uncarveR : ltac2:(tb__ "0|6|
Sa8S96S80S3S2dS46Q40A1A1S2dS5cA1M0S118S5dS2dSbA1M1S2dS109A1Sa9RaA1S3eG1S19S81R9A1A1S35SbR3SafS109SbS10bR2A4A3A3S3eS31S111Sf9R3A2S30A3S3eSa6S99RcA1S9eA3S3eS31S98SaS81RcA1A1RdA2S30A3S6bS45S10aVAInv;VCST;VXGL;S8aVrho0;VP0;S2fS2eS0S0A2M2A1M3S2fS2eG2S0A2A1M4S8dVk;A1M5VPA;RfReAcRdRcRbS38G0S136RaS137R9R8A2A4A6S6bS45S10aVAInv;VCST;VXGL;S8aVrho0;VP0;G3G4G5VPA;R10RfAcS83ReS14cS81ReA1R8A2A2S129RdSafS109SbS10bR7A4S154R9RcRaA3A3RcS38G0S136RbS137RaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
S10dVAInv;VCST;VXGL;VALA;VHLV;S8aVrho0;VP0;S2fS2eS0S0A2M0A1S2fS2eG0S0A2A1S8dVk;A1VPA;Sf9S14aSfbSfeVAInv;VCST;VHCSTok;VHLPP;A4A10").
End KV.

Lemma holds_fact : ltac2:(tb__ "0|0|
S3S2dS6A1S6Sb0S6ScR3A1R2A3S3eS31ScaS6SdR2A1R3A3S30A3ScR5R3A2F_;F_;Fq;Ffacts;Frho;").
Proof. intros rho facts q HF H. exact (holds_mem _ _ _ HF H). Qed.

Lemma U_SPUle_lit_r : ltac2:(tb__ "0|0|
S3S2dS6A1S5S0Sb0S6ScR4A1R3A3S3eS31ScaS6SdS17R3S8R2A1A2A1R4A3S30A3S3fS4aZ0R3A2S4cR3S4eZ2Z40A2A2A2S4aS47Q40S7R7R5A2A2R4A2F_;F_;F_;Fz;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e z HF H Hz. pose proof (holds_fact rho facts _ HF H) as X. cbn [holds] in X. rewrite U_lit in X.
  rewrite <- M64v_eq in X. rewrite Z.mod_small in X by lia. exact X.
Qed.

Lemma SHR_now : ltac2:(tb__ "0|1|
Sa8S3S3OF_;S0S96Sc7S0S3S2dS46Q40A1A1S2dS5cA1S5dS3RaR1A1S8cR2A1F_;Fr;S9bVAInv;VCST;VXGL;S8aRcRbRaS2fS2eS0S0A2M0A1S2fS2eG0S0A2A1S8dR9A1VPA;R8R7R6R5R4R3R2A12S8cR6A1F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k nd Ai kc rho tp tr md HP HJ. split.
  -
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
    destruct (HP _ HP0) as [[HZ HPr] _]. destruct HK0 as [K1 K2]. split.
    + intros a Ha. rewrite (K1 a ltac:(lia)); [exact (HZ a Ha)|].
      right. split; [|intro HcN; pose proof (HZ a Ha) as HcE; congruence]. exists (8 * (a - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
      * left. right. left. split; [apply HCSTdrv; exists 0x644ca8, 0x450; split; [cbn; tauto | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
      * unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    + intros a Ha. rewrite (K1 a ltac:(lia)); [exact (HPr a Ha)|].
      right. split; [|intro HcN; pose proof (HPr a Ha) as HcE; congruence]. exists (8 * (a - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
      * left. right. left. split; [|unfold errno_addrA, ERRNO_A, SHADOW_OFF; destruct Ha; lia]. apply HCSTdrv. destruct Ha as [R|R].
        -- exists 0x22b80, 0xf00. split; [cbn; tauto | unfold SHADOW_OFF; lia].
        -- exists 0xec540, 0x1800. split; [cbn; tauto | unfold SHADOW_OFF; lia].
      * unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
  - eapply SHR_kept; [exact HP | exact HJ].
Qed.

Lemma JR_refds : ltac2:(tb__ "0|3|
S2dS2eS46Q40A1M0S5eA2A1M1G1S2dS5cA1M2S3S3OF_;S0S96S3S2dG0A1G2S5dG1S3eG1R1RbA3S56S59RdRbA2RaR9R8R7R6R5R4R3A9S56S59RdRcA2RbRaR9R8R7R6R5S67R3R4A2A9F_;F_;Ff;Fmd;Ftr;Ft;Frho;Fnd;Fk;FP0;Frho0;Fevs;Ffds';Ffds;").
Proof.
  intros fds fds' evs rho0 P0 k nd rho t tr md f -> (Ai & kc & Hav & (Htr & Hfd & HX) & HM & REST).
  exists Ai, kc. split; [exact Hav|]. split; [|split; [apply HLF; exact HM | exact REST]].
  split; [exact Htr|]. split; [apply m_fds_with_fds | apply HMDXfds; exact HX].
Qed.

Lemma dst_ranges : ltac2:(tb__ "0|c|
S3S5S4aS47Q40M0S7R2S101A2A2S102A2S4aS47G0S7R3S104A2A2S4eZ2M1Z1aA2A2S4aS47G0S7R4R3A2A2Z10000A2S3fS3eS2eS0S0A2M2SeR5Sf1R4A1M3A2M4SeR5Sf0R4A1M5A2M6A3S3fS3eG2G6G4A3S3fS4aS15R5G3A2M7S13R5G3A2M8A2S3fS4cS50G8G7A2S4eG1Z3fA2M9A2S3fS4aS15R5G5A2MaS13R5G5A2MbA2S4cS50GbGaA2G9A2A2A2A2A2A2F_;F_;F_;Fr;Frho;").
Proof.
  intros rho r HB HL HW. unfold O_dstL, O_dstC, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  pose proof (urange (eval rho vB)). pose proof (urange (eval rho vLen)). pose proof (urange (eval rho r)).
  assert (E1 : bv_unsigned (eval rho (add vB vLen)) = bv_unsigned (eval rho vB) + bv_unsigned (eval rho vLen)).
  { unfold add. rewrite U_add. rewrite <- M64v_eq. apply Z.mod_small. unfold ATOPHI in HB. lia. }
  assert (E2u : bv_unsigned (eval rho (add vLen r)) = bv_unsigned (eval rho vLen) + bv_unsigned (eval rho r)).
  { unfold add. rewrite U_add. rewrite <- M64v_eq. apply Z.mod_small. lia. }
  assert (E2 : soff rho (add vLen r) = bv_unsigned (eval rho vLen) + bv_unsigned (eval rho r)).
  { unfold soff. rewrite signed_small by (rewrite E2u; lia). exact E2u. }
  assert (E3 : soff rho vLen = bv_unsigned (eval rho vLen)) by (unfold soff; rewrite signed_small by lia; reflexivity).
  assert (E4 : soff rho r = bv_unsigned (eval rho r)) by (unfold soff; rewrite signed_small by lia; reflexivity).
  rewrite !soff_lit_small by lia. rewrite E1, E2, E3, E4. repeat split; try lia; f_equal; lia.
Qed.

Lemma rds_ranges : ltac2:(tb__ "0|b|
S3S5S5S2dS9A1S3eS0S47Q40M0S7R4R3A2A2Sd4A3S4aS47G0S7R5R3A2A2Z10000A2S3fS3eS2eS0S0A2M1SeR6Sd9R4R3A2M2A2M3SeR6S1fR5S8Z0A1R4R3S1dA5M4A2M5A3S3fS3eG1G5G3A3S3fS4aS15R6G2A2M6S13R6G2A2M7A2S3fS4cS50G7G6A2S4eZ2Z3fA2M8A2S3fS4aS15R6G4A2M9S13R6G4A2MaA2S4cS50GaG9A2G8A2A2A2A2A2A2F_;F_;Fcs;Fw;Fb;Frho;").
Proof.
  intros rho b w cs E0 HW. unfold O_rdsL, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  pose proof (urange (eval rho w)).
  assert (E2u : bv_unsigned (eval rho (add (SLit RS) w)) = RS + bv_unsigned (eval rho w)).
  { unfold add. rewrite U_add, U_lit. rewrite <- !M64v_eq. rewrite (Z.mod_small RS) by (unfold RS, RD_STAGE; lia). apply Z.mod_small. unfold RS, RD_STAGE. lia. }
  assert (E2 : soff rho (add (SLit RS) w) = RS + bv_unsigned (eval rho w)).
  { unfold soff. rewrite signed_small by (rewrite E2u; unfold RS, RD_STAGE; lia). exact E2u. }
  assert (E4 : soff rho w = bv_unsigned (eval rho w)) by (unfold soff; rewrite signed_small by lia; reflexivity).
  rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). rewrite !U_lit. rewrite <- !M64v_eq. change (0 mod 2 ^ 64) with 0.
  rewrite E0, E2, E4. unfold RS, RD_STAGE. repeat split; try lia; f_equal; lia.
Qed.
Lemma U_rdsb : ltac2:(tb__ "0|0|
S3S3eS0S47Q40S7R1Sf6A2A2Sd4A3Frho;").
Proof. intros rho. unfold rdsb, add. rewrite U_add, !U_lit. reflexivity. Qed.
Lemma U_RS : ltac2:(tb__ "0|0|
S3S3eS0S47Q40S7R1S8Sd4A1A2A2Sd4A3Frho;").
Proof. intros rho. rewrite U_lit. reflexivity. Qed.

Lemma JR_tv_band_free : ltac2:(tb__ "0|1|
Sa8S3S3OF_;S0S96S3S2dS46Q40A1A1S2dS5cA1S5dS2eS5S5A2M0S56RaR9R8R7R6R5R4R3R2A9ScbG0R2S9aR7A1A3S156R7R3A2SaeSbeR8S39S5S5R4A3A2SbeR8S3aS5S5R4A3A2A2F_;F_;F_;Ft;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k nd rho tp tr md t (Ai & kc & HJ) Hin Hnz.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _).
  destruct (proj1 (Forall_forall _ _) HN t Hin Hnz) as (Hpos & Hlive & _).
  unfold tvv in Hpos, Hlive. cbn [fst snd bx2] in Hpos, Hlive |- *. unfold uval in *.
  apply band_free_of_points; [lia|]. intros a Ha.
  pose proof (law_client_app _ _ _ ALA Ai rho tp md a HM) as X. pose proof (topG_range (aa_geom Ai)) as TG.
  assert (HC : client_addrA CST Ai a).
  { left. right. left. exists (uval rho (fst t)), (uval rho (snd t)). split; [exact Hlive | exact Ha]. }
  specialize (X HC). unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Lemma JR_tv_bandfree : ltac2:(tb__ "0|0|
Sa8S3S3OF_;S0S96S3S2dS46Q40A1A1S2dS5cA1S5dS56R9R8R7R6R5R4R3R2R1A9S110R5S9aR6A1A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k nd rho tp tr md HJ t Ht Hz a Ha.
  pose proof (JR_tv_band_free Kc rho0 P0 k nd rho tp tr md t HJ Ht Hz) as X. unfold band_free in X. lia.
Qed.

Lemma rds_clsZ : ltac2:(tb__ "0|1|
S3S1S1S3eS0S47Q40M0S4R3R2A2A2Sd4A3S4aS47G0S4R4R2A2A2Z10000A2S161R5R4R3A3F_;F_;Fil;Fib;Fr;").
Proof. intros r ib il H1 H2. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ. right. rewrite H1. unfold RS, RD_STAGE, SHB. lia. Qed.

Lemma triple_pre : ltac2:(tb__ "0|1|
S74S71OF_;OS71R4R1A1R3F_;Fw;R2S70S45R5R4A3M0F_;G0F_;F_;FX;FQ';FP;").
Proof. intros P Q' X H1 H2 w Hw. exact (H2 (H1 w Hw) w Hw). Qed.

Lemma SPA_JR_facts : ltac2:(tb__ "0|0|
Sa8S3S3OF_;S0S96S80S3S2dS46Q40A1A1S71S6bS45S56R9R8R7R6R5A5R4R3R2R1A6S3fR8R9A1S3fS12cS8aR9R4A3Sb0S6ScR4A1S12S81R5A1A1A3A2A2F_;Fw;Ftp;Frho;FA;Fnd;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k nd A rho tp w [Hsm HJ]. destruct (JR_P0 _ _ _ _ _ _ _ _ _ HJ) as [H1 H2].
  split; [exact H1|]. split; [exact H2|]. exact (smatchA_facts segs _ _ _ _ Hsm).
Qed.

Lemma bound_facts : ltac2:(tb__ "0|3|
S3S2dS6A1Sb0S6ScR2A1R1A3S3eS31ScaS6SdS17S101S8S102A1A2A1R2A3S30A3S3eS31ScaS6SdS17S104S108A2A1R3A3S30A3S3eS31ScaS6SdS17S108S8S4eZ2Z1aA2M0A1A2A1R4A3S30A3S3eS31ScaS6SdS17Sd6S8Z10000M1A1A2A1R5A3S30A3S3fS4aS47Q40M2S7R7S101A2A2S102A2S3fS4aS47G2S7R7S104A2A2G0A2S4aS47G2S7R7Sd6A2A2G1A2A2A2F_;F_;F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H1 H2 H3 H4.
  pose proof (U_SPUle_lit_r rho facts vB ATOPHI HF H1 ltac:(unfold ATOPHI; lia)) as A1.
  pose proof (holds_fact rho facts _ HF H2) as A2. cbn [holds] in A2.
  pose proof (U_SPUle_lit_r rho facts vCap (2 ^ 26) HF H3 ltac:(lia)) as A3.
  pose proof (U_SPUle_lit_r rho facts vWant 65536 HF H4 ltac:(lia)) as A4.
  change (eval rho vCap) with (rw rho 41%positive) in A3. change (eval rho vLen) with (rw rho 42%positive) in A2 |- *.
  change (eval rho vCap) with (rw rho 41%positive) in A2. repeat split; try lia.
Qed.

Lemma cap_le : ltac2:(tb__ "0|1|
S36Sc5R1UaA2S3fS4aZ10000S8bR2A1M0A2S4aG0S4eZ2Z1aA2A2A2F_;Fg;").
Proof.
  intros g Hg. unfold cap. split; [pose proof (Z.pow_pos_nonneg 2 (Z.of_nat g)); nia|].
  change (2 ^ 26) with (65536 * 2 ^ 10). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma SPA_JR_takeK : ltac2:(tb__ "0|5|
Sa8S3S3OF_;S0S0S2dS2eS5S5A2A1S2dSb4A1S80S3S2dS46Q40A1A1S71S3fS4aZ0M0R7A2S4aR7R8A2A2S3eS31Sb7R6A1S30A3S6bS45S97VAInv;VCST;VXGL;S8aRdRcRbS2fS2eS0S0A2M1A1M2S2fS2eG1S0A2A1M3S8dRaA1VPA;S9fR8S2fS2eS2eS5S0A2S5A2A1M4R7S9eA4AcR6R5R4R3A6S6bS45S97VAInv;VCST;VXGL;S8aReRdRcG2G3S8dS50RbRaA2A1VPA;S9fR9G4S35Sb4R8S37Sb4SbfG0Z1RaA3S2fSb4A1A3A3S9eA4AcR7R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;FA;Fbd;Ftv;Fc;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k c tv bd A rho tp w Hc Hw [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  apply (JAi_rebud Kc rho0 P0 (BXk k) (BXk (k - c)) (NDA tv [] bd ANone) (bd ++ [BIc 0 1 c]) Ai kc rho tp); [reflexivity | cbn; lia | cbn; lia | | | exact HJ].
  - unfold bd_wpos in *. rewrite forallb_app, Hw. reflexivity.
  - intros V Km Kf HB. cbn [nd_bd nd_am] in HB |- *. destruct HB as (_ & _ & _ & _ & _ & _ & Hnn & _).
    rewrite bsumV_app, bsumK_app. cbn [bsumV bsumK bival lfval bi_f bi_c bi_v bi_k BIc]. unfold bxa, BXk. cbn [fst snd bx2].
    assert (BV : bival rho (BIc 0 1 c) = c) by reflexivity. rewrite BV.
    split; [|lia]. unfold bd_nn in *. apply Forall_app. split; [exact Hnn|]. constructor; [rewrite BV; lia | constructor].
Qed.

Lemma SPA_JR_dropBX : ltac2:(tb__ "0|3|
Sa8S3S3OF_;S0S96S80S3S2dS46Q40A1A1S71S4aZ0R6A2S6bS45S97VAInv;VCST;VXGL;S8aRaR9R8S2fS2eS0S0A2M0A1M1S2fS2eG0S0A2A1M2S8dR7A1VPA;R6AcR5R4R3R2A6S6bS45S97VAInv;VCST;VXGL;S8aRbRaR9G1G2Sf8VPA;R7AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fnd;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k nd A rho tp w Hk [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  destruct nd as [tv fr bd am].
  apply (JAi_rebud Kc rho0 P0 (BXk k) BX0 (NDA tv fr bd am) bd Ai kc rho tp); [reflexivity | cbn; lia | cbn; lia | | | exact HJ].
  - destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBU & _). destruct HBU as (_ & _ & _ & _ & _ & Hw & _). exact Hw.
  - intros V Km Kf HB. cbn [nd_bd nd_am] in HB |- *. destruct HB as (_ & _ & _ & _ & _ & _ & Hnn & _).
    unfold bxa, BXk, BX0. cbn [fst snd bx2]. split; [exact Hnn|]. lia.
Qed.

Lemma q_cleanup : ltac2:(tb__ "0|7|
Sa8S3S3OF_;S0S80S80S80S80S80S3S2dS46Q40M0A1M1A1S71Sa9RcA1S3eS34S80A1M2S157R9Sf4A2S33S80R8A2A3S3eS34SbA1SceSbS19S81R9A1M3A1U26M4A3S33SbSf3Sd6S2fS9A1M5A2A2A3S3eSfS168S81RaA1M6G4Sd9Sd6G5A2A3G3A3S3eS31S162S81RbA1G6A2S30A3S3eS2dS2eS5S5A2A1S84RbA1S84RcA1A3S3eS5S86RcA1S86RdA1A3S3eG2S157RdS37S158S159G4A1S2fS158A1A3A2S33S80RcA2A3S3eS2dSbA1S19S81RdA1A1S35SbSeeRdA1SafS109SbS10bS7aA4A3A3S3eS31S98SaS81ReA1A1S75A2S30A3S3eS31S16aSdfS84RfA1A2S30A3S3eS80S166S83R10S14cS81R10A1SeeR10A1A2A2SdfA2RfA3S4aS47G0S7RfSd6A2A2Z10000A2S3R18R1A1Sf7R2A1F_;Fr;S6bS45S56R1aR19R18R17S75A5R16R11R10RfA6S41S3S3S3fS1S3eG1S4R2R1A2S4R14R1A2A3Fv;S6bS45S56R1cR1bR1aR19S75A5R14R1R12R11A6A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FQd;FQc;FQb;FQa;FLf;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k Lf Qa Qb Qc Qd rho tp w HKc Xa Hn Hset Hsame HXb Hbb Xc Hobjs Hnb HX HQd HW HP0 HS.
  destruct w as [tr [ms md]].
  apply (SPA_axforms segs _ XF_q rho Lf Qa tp _ Xa) in HS.
  destruct (rds_ranges rho (SLit RS) vWant [] (U_RS rho) HW) as (RR1 & _ & RR2 & RR3 & _ & _).
  apply (SPA_reslice segs _ rho Qa 38 _ (O_rdsL vWant []) tp _ Hn eq_refl eq_refl eq_refl eq_refl ltac:(rewrite Hset; exact Hsame) RR1 RR2 RR3) in HS.
  rewrite Hset in HS.
  assert (EQb : ax_setS Qa (ax_S Qb) = Qb) by (destruct Qa, Qb; cbn in HXb, Hbb |- *; subst; reflexivity). rewrite EQb in HS.
  apply (SPA_axforms segs _ [AXMerge 38] rho Qb Qc tp _ Xc) in HS.
  pose proof (uncarveR rho0 P0 k HP0 Kc nd_R Qc rho tp tr ms md (objs37 Qc) N_rd HKc Hobjs N_rd_un eq_refl Hnb HS) as HS2.
  set (rho' := rho_absorb rho (map lc_obj N_rd) (vms md tp ms)) in HS2. exists rho'. split; [intros v; reflexivity|].
  rewrite <- HQd. apply SPA_x_sub; [exact (xrs_inclb_sound _ _ HX) | exact HS2].
Qed.

Lemma bk_cleanup : ltac2:(tb__ "0|2|
Sa8S3S3OF_;S0S80S80S80S80S80S80S3S2dS46Q40M0A1M1A1S71Sa9RdA1S7cSefSdfRaR9R8R7R6R5A8S4aS47G0S7R5S101A2A2S102A2S4aS47G0S7R6S104A2A2S4eZ2Z1aA2A2S4aS47G0S7R7SefA2A2Z10000A2S3R11R1A1Sf7R2A1F_;Fr;S6bS45S56R13R12R11R10S75A5RfR9R8R7A6S41S3S3S3fS1S3eG1S4R2R1A2S4RcR1A2A3Fv;S6bS45S56R15R14R13R12S75A5RcR1RaR9A6A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FB;FBd;FBc;FBb;FBa;FLf;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k Lf Ba Bb Bc Bd B rho tp w HKc HB HvB HvL HvR HP0 HS.
  destruct HB as (Xa & Hn1 & Hset1 & Hs1 & HXb & Hbb & Hn2 & Hset2 & Hs2 & HXc & Hbc & Xd & Hobjs & Hnb & HX & HBe & _ & _).
  destruct w as [tr [ms md]].
  apply (SPA_axforms segs _ XF_bka rho Lf Ba tp _ Xa) in HS.
  destruct (dst_ranges rho vRes1 HvB HvL HvR) as (DR1 & _ & DR2 & DR3 & _ & _).
  apply (SPA_reslice segs _ rho Ba 11 _ (O_dstL vRes1) tp _ Hn1 eq_refl eq_refl eq_refl eq_refl ltac:(rewrite Hset1; exact Hs1) DR1 DR2 DR3) in HS.
  rewrite Hset1 in HS.
  assert (EQb : ax_setS Ba (ax_S Bb) = Bb) by (destruct Ba, Bb; cbn in HXb, Hbb |- *; subst; reflexivity). rewrite EQb in HS.
  destruct (rds_ranges rho (SLit RS) vRes1 [] (U_RS rho) HvR) as (RR1 & _ & RR2 & RR3 & _ & _).
  apply (SPA_reslice segs _ rho Bb 41 _ (O_rdsL vRes1 []) tp _ Hn2 eq_refl eq_refl eq_refl eq_refl ltac:(rewrite Hset2; exact Hs2) RR1 RR2 RR3) in HS.
  rewrite Hset2 in HS.
  assert (EQc : ax_setS Bb (ax_S Bc) = Bc) by (destruct Bb, Bc; cbn in HXc, Hbc |- *; subst; reflexivity). rewrite EQc in HS.
  apply (SPA_axforms segs _ XF_bkb rho Bc Bd tp _ Xd) in HS.
  pose proof (uncarveR rho0 P0 k HP0 Kc nd_R Bd rho tp tr ms md (objs37 Bd) N_mc HKc Hobjs N_mc_un eq_refl Hnb HS) as HS2.
  set (rho' := rho_absorb rho (map lc_obj N_mc) (vms md tp ms)) in HS2. exists rho'. split; [intros v; reflexivity|].
  rewrite <- HBe. apply SPA_x_sub; [exact (xrs_inclb_sound _ _ HX) | exact HS2].
Qed.

Lemma U_len1 : ltac2:(tb__ "0|2|
S3S0S0S3eS0S47Q40M0S4R3P65A2A2R1A3S3eS0S47G0S4R4P2aA2A2R3A3S4aZ0R4A2M1G1S4cS4bR6R5A2S4eZ2Z3eA2A2S3eS0S47G0S7R8S7eA2A2S4bR7R6A2A3F_;F_;F_;F_;F_;Fres;Flen;Frho;").
Proof.
  intros rho len res H1 H2 HL HR HS. unfold len1, add. rewrite U_add. change (eval rho vRes1) with (rw rho 101%positive). change (eval rho vLen) with (rw rho 42%positive).
  rewrite H1, H2, <- M64v_eq. rewrite Z.mod_small; lia.
Qed.

Lemma P0R1_SHR : ltac2:(tb__ "0|0|
S36S0S3S91R3R2VF;R1A4S8cR2A1F_;Fr;Flen;Fg;").
Proof. intros g len r (_ & _ & _ & _ & H). exact H. Qed.
Lemma P0RD1_SHR : ltac2:(tb__ "0|0|
S36S0S0S3S8eR4R3R2VF;R1A5S8cR2A1F_;Fr;Fwant;Flen;Fg;").
Proof. intros g len want r [H _]. eapply P0R1_SHR; exact H. Qed.

Lemma U_sll1 : ltac2:(tb__ "0|2|
S3S5S4cS47Q40M0S7R2R1A2A2S4eZ2M1Z3eA2A2S3eS0S47G0S7R3S1eS141R2S8Z1A1A3A2A2S4fG1S47G0S7R3R2A2A2A2A3F_;Fe;Frho;").
Proof.
  intros rho e He. cbn [eval]. rewrite sll_val. change (1 mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (urange (eval rho e)). rewrite Z.mod_small; lia.
Qed.
Lemma U_srl26 : ltac2:(tb__ "0|2|
S3S5S3eS0S47Q40M0S7R2S1eS142R1S8Z1aM1A1A3A2A2S53S47G0S7R2R1A2A2S4eZ2G1A2A2A3Fe;Frho;").
Proof. intros rho e. cbn [eval]. rewrite srl_val. change (26 mod 64) with 26. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma P0G_SHR : ltac2:(tb__ "0|0|
S36S3S93R2VF;R1A3S8cR2A1F_;Fr;Fg;").
Proof. intros g r (_ & _ & _ & H). exact H. Qed.
Lemma cap_lt26 : ltac2:(tb__ "0|1|
S36Sc5R1UaA2S4cS8bR2A1S4eZ2M0Z1aA2A2S4aS8bR3A1S4eG0Z19A2A2F_;F_;Fg;").
Proof.
  intros g Hg Hlt. unfold cap in *. destruct (Nat.eq_dec g 10) as [->|Hne].
  - exfalso. change (Z.of_nat 10) with 10 in Hlt. lia.
  - change (2 ^ 25) with (65536 * 2 ^ 9). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Section ReadStep1.
Variables (g : nat) (len want k : Z) (rho0 : valuation).
Definition res1 : Z := ltac2:(tb__ "0|0|
S54Vwant;S50S4dS32S46Q8A1VF;A2A1Vlen;A2A2").
Definition BS1 : list byte := ltac2:(tb__ "0|1|
Sb1S46Q8A1M0S52Vwant;A1Sb2G0S52Vlen;A1VF;A3A3").
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
S8eVg;Vlen;Vwant;VF;A4").
Hypothesis Hg : (g <= 10)%nat.
Hypothesis Hlen : 4 <= len.
Hypothesis Hlw : ltac2:(tb__ "0|0|
S4aS4bVlen;Vwant;A2S8bVg;A1A2").
Hypothesis Hw : 1 <= want <= 65536.
Hypothesis HlenF : ltac2:(tb__ "0|0|
S4aVlen;S4dS32S46Q8A1VF;A2A1A2").
Hypothesis Hk : 0 <= k.

Hypothesis Hcopy : ltac2:(tb__ "0|1|
S4aZ1S119A2S3S2dS46Q40M0A1A1S3eS0S47G0S4R2P65A2A2S119A3S70S45S6bS45S56S57S4bVlen;S119A2A1Vrho0;VP0;Vk;S75A5Se8R3R2A5VQ;A3F_;Ftp';Frho';F_;").
Hypothesis Hclose : ltac2:(tb__ "0|0|
S3eS0Vlen;S4dS32S46Q8A1VF;A2A1A3S3S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5Se3R2R1A5VQ;A3Ftp';Frho';F_;").

Lemma BS1_len : Z.of_nat (length BS1) = res1.
Proof. unfold BS1, res1. rewrite length_firstn, length_skipn. lia. Qed.

Definition J0rd (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S2dS5cA1S5dS3fS56S57Vlen;A1Vrho0;VP0;Vk;S75Vrho1;R3R2R1A9S3eS0S47G0S4R4P13A2A2Vwant;A3A2Lmd;Ltr;Lt;Lr;").
Definition J1rd (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S2dS5cA1S5dS3fS56S57S4bVlen;S119A2A1Vrho0;VP0;Vk;S75Vrho1;R3R2R1A9S3eS0S47G0S4R4P64A2A2S119A3A2Lmd;Ltr;Lt;Lr;").

Lemma nd_R_NF : ltac2:(tb__ "0|0|
S3eS31S98S8aS75A2S30A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma J0rd_stable : ltac2:(tb__ "0|0|
S3S6cS45S8aS11aR1A1A3Frho1;").
Proof.
  intros rho1 r r' t tr md md' Hag Hme [HJ Hv]. split.
  - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_R Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) nd_R_NF (agree_below_refl _ _) Hme HJ').
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 19%positive ltac:(cbv; reflexivity)). exact Hv.
Qed.
Lemma J1rd_stable : ltac2:(tb__ "0|0|
S3S6cS45P65S11bR1A1A3Frho1;").
Proof.
  intros rho1 r r' t tr md md' Hag Hme [HJ Hv]. split.
  - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_R Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) nd_R_NF (agree_below_refl _ _) Hme HJ').
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 100%positive ltac:(cbv; reflexivity)). exact Hv.
Qed.

Lemma rd_bs : ltac2:(tb__ "0|0|
S3S3eS0S47Q40S4R1P13A2A2Vwant;A3S3eS2dS46Q8A1A1S12dSc6R2VF;Vlen;A4S11cA3F_;Fr;").
Proof.
  intros r Hv. unfold rbA_bs, BS1. rewrite rd_H12. change (eval r vC) with (rw r 19%positive). rewrite Hv. reflexivity.
Qed.

Lemma J0rd_fd : ltac2:(tb__ "0|2|
S3S3S2dS46Q40M0A1A1S2dS5cA1S5dS11aR5R4R3R2R1A5S3fS3eS34S5eA1S61S63R2A1S48G0Z3A2A2S33S5eS64Vp3;S48G0S3Vlen;L_;R5A1A2A2A2A3S3eS34S2dS46Q8A1A1M1A1S120S5fR2A1Vp3;A2S33G1VF;A2A3A2F_;Fmd;Ftr;Ft;Fr;Frho1;").
Proof.
  intros rho1 r t tr md [HJ _]. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & HX). rewrite Hfds. split; [apply HFDS3 | apply HMDXfs; exact HX].
Qed.

Lemma J0rd_K : ltac2:(tb__ "0|1|
S3S3S2dS46Q40A1A1S2dS5cA1S5dS11aR5R4R3R2R1A5S11bR6S12fSc6R5VF;S3Vlen;L_;R5A1M0A4R4R3S12eSc6R5Vp3;VF;G0R2A6A5F_;Fmd;Ftr;Ft;Fr;Frho1;").
Proof.
  intros rho1 r t tr md [HJ Hv]. cbn beta. pose proof BS1_len as BL. pose proof (cap_le g Hg) as HC. split.
  - unfold rbA_md'. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & HX).
    eapply JR_refds; [|exact HJ]. rewrite Hfds. rewrite (rd_bs r Hv). unfold len_word. rewrite BL. apply HFDSstep; unfold res1; lia.
  - unfold rkA_rho'. rewrite rd_next. rewrite rho_set_rw_at. rewrite (rd_bs r Hv). unfold len_word. rewrite BL.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. unfold res1; lia.
Qed.

Lemma step_rd1 : ltac2:(tb__ "0|0|
S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5SedVrho0;R1A5VQ;A3Ftp;").
Proof.
  intros tp. pose proof (cap_le g Hg) as HC.
  destruct rd1_site as (Hnode & HerrV & Sp1 & Sp2 & Sp3 & Hn3 & Hset3 & Hs3 & Hcv & HC1 & HnodeC & Hfw).
  destruct (node_okb_sound _ _ Hnode) as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (node_okb_sound _ _ HnodeC) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct rd1_call as (Hs19 & Hs17 & Hs15 & Hs16 & Hpb & Himp & Hplt & HnodeT & HLVT).
  destruct (node_okb_sound _ _ HnodeT) as (T1 & T2 & T3 & T4 & T5 & T6).
  eapply JR_run; [exact Hk | exact (proj2 run_RD) | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. intros HF1.
  pose proof (U_SPUle_lit_r rho1 _ vWant 65536 HF1 Hfw ltac:(lia)) as HW1.

  eapply (etriple_conseq (P := SPA segs (JR (KcR len) rho0 P0 k nd_R) C_rd1 rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { apply (SPA_errV _ rho1 E_rd1 tp w HerrV) in HS. fold A0_rd1 in HS.
    apply (SPA_split segs _ rho1 A0_rd1 0 (SLit (-2256)) _ tp w Sp1) in HS. change (ax_setS A0_rd1 (ax_S A1_rd1)) with A1_rd1 in HS.
    apply (SPA_split segs _ rho1 A1_rd1 0 (SLit (-2336)) _ tp w Sp2) in HS. change (ax_setS A1_rd1 (ax_S A2_rd1)) with A2_rd1 in HS.
    apply (SPA_split segs _ rho1 A2_rd1 _ (add (SLit RS) vWant) _ tp w Sp3) in HS. change (ax_setS A2_rd1 (ax_S A3_rd1)) with A3_rd1 in HS.
    destruct (rds_ranges rho1 rdsb vWant [] (U_rdsb rho1) HW1) as (_ & CR1 & _ & _ & CR2 & CR3).
    apply (SPA_reslice segs _ rho1 A3_rd1 (irds A3_rd1) _ (O_rdsC vWant []) tp w Hn3 eq_refl eq_refl eq_refl eq_refl ltac:(rewrite Hset3; exact Hs3) CR1 CR2 CR3) in HS.
    rewrite Hset3 in HS. change (ax_setS A3_rd1 (ax_S A4_rd1)) with A4_rd1 in HS.
    unfold carve_chk in Hcv. apply andb_prop in Hcv as [Hcv Hb6]. apply andb_prop in Hcv as [Hw6 Hc6]. apply sv_eqb_sound in Hb6.
    rewrite <- HC1. apply (carveR rho0 P0 k (P0RD1_SH g len want F) (KcR len) nd_R A4_rd1 rho1 tp w N_rd (ss_next (ax_S A4_rd1)) HS Hw6 (Pos.leb_refl _) Hb6 Hc6). }

  apply (pure_callJ_v_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA (KcR len) (KcR (len + res1)) C_rd1 Pre_rd s_rd1 R_rd1 (Posts_rd [] 100) rho1 tp nd_R
           (J0rd rho1) (J1rd rho1) Q (KcG_ok _ _)).
  - intros rho2 tp2. apply (read_keep_sum_ex (J0rd rho1) (J1rd rho1) p3 F (fun _ => len) (J0rd_stable rho1) (J1rd_stable rho1)
                             ltac:(intros r; unfold res1 in *; lia) (J0rd_fd rho1) (J0rd_K rho1) rho2 tp2).
  - exact fr_rd1.
  - exact cc_rd1k.
  - exact M1.
  - exact M3.
  - exact M4.
  -   intros tr ms md Hsm HJ. split; [exact HJ|].
    cbn [rho_sub rw]. rewrite Hs19. rewrite eval_absorb. change (eval rho1 vWant) with (rw rho1 49%positive).
    destruct (JR_P0 _ _ _ _ _ _ _ _ _ HJ) as [[_ HP49] Hav]. rewrite <- (U_agree rho0 rho1 49%positive Hav ltac:(cbv; reflexivity)) in HP49. exact HP49.
  -   intros rhoL tr' md' [HJ' _]. exact HJ'.
  -
    intros L rho' rhoL tr' md' HinL Hag' [HJ' Hres] Hpv. destruct HinL as [<-|[]]. cbn [la_state] in Hpv |- *.
    assert (HR : bv_unsigned (rw rho' 101%positive) = res1).
    { pose proof (Hpv 100%positive Hpb ltac:(apply Nat.ltb_lt; exact Hplt)) as E. rewrite Himp in E. unfold vRes1 in E. cbn [eval] in E. rewrite <- E. exact Hres. }
    change (ax_add_facts (ss_facts (ax_S C_rd1)) (import_postA s_rd1 Pre_rd (P_rd [] 100) C_rd1 R_rd1)) with (T_after Pre_rd C_rd1 s_rd1 R_rd1 (P_rd [] 100)).
    destruct T_rd_eqs as (_ & ET & _ & EL & _ & HokL). rewrite ET.
    apply (errL_Te _ T_rd1k' _ rho' tp HokL (JR_blind (KcR (len + res1)) rho0 P0 k NF nd_R nd_R_NF)). intros rhoE HrwE _ _. rewrite EL.
    rewrite <- HrwE in HR. rename rho' into rhoO'. rename rhoE into rho'.
    pose proof (proj2 run_T) as RT. rewrite HLVT in RT.
    eapply JR_run; [exact Hk | exact RT | exact T2 | exact T1 | exact T3 |].
    intros Lf rho5 HinLf Hag5. destruct HinLf as [<-|[<-|[]]]; cbn [la_state].
    +
      destruct rd1_cont as (Xa & Kn & Kset & Ks & Xc & Kobjs & Knb & KX & KQ & KnodeQ & Kne & Kfw).
      apply etriple_factsA. intros HF5.
      pose proof (U_SPUle_lit_r rho5 _ vWant 65536 HF5 Kfw ltac:(lia)) as HW5.
      assert (HR5 : bv_unsigned (rw rho5 101%positive) = res1).
      { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 101%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
      assert (Hres1 : 1 <= res1).
      { pose proof (holds_fact rho5 _ _ HF5 Kne) as X. unfold vRes1 in X. cbn [holds eval branch_taken] in X. unfold bv_eqb in X.
        rewrite lit_unsigned in X. change (0 mod 2 ^ 64) with 0 in X. destruct (Z.eqb_spec (bv_unsigned (rw rho5 101%positive)) 0) as [E0|NE]; [cbn in X; discriminate|].
        pose proof BS1_len. unfold res1 in *. lia. }
      eapply (etriple_conseq (P := fun w => exists rho6, bv_unsigned (rw rho6 101%positive) = res1 /\ SPA segs (JR (KcR (len + res1)) rho0 P0 k nd_R) Q1 rho6 tp w));
        [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (q_cleanup (KcR (len + res1)) rho0 P0 k Lcp1 Q1a Q1b Q1c Q1 rho5 tp w (KcG_ok _ _) Xa Kn Kset Ks eq_refl eq_refl Xc Kobjs Knb KX KQ HW5 (P0RD1_SH g len want F) HS)
          as (rho6 & Hv6 & HS6). exists rho6. split; [rewrite Hv6; exact HR5 | exact HS6]. }
      apply etriple_ex. intros rho6.
      apply (triple_pre _ _ (bv_unsigned (rw rho6 101%positive) = res1)); [intros w [H _]; exact H | intros HR6].
      eapply (etriple_conseq (P := SPA segs (JR (KcR (len + res1)) rho0 P0 k nd_R) Q1 rho6 tp)); [intros w [_ HS]; exact HS | intros w' Hw'; exact Hw' |].
      exact (Hcopy Hres1 rho6 tp HR6).
    +
      destruct rd1_close as (Xa & Kn & Kset & Ks & Xc & Kobjs & Knb & KX & KQ & KnodeQ & Keq & Kfw).
      apply etriple_factsA. intros HF5.
      pose proof (U_SPUle_lit_r rho5 _ vWant 65536 HF5 Kfw ltac:(lia)) as HW5.
      assert (HR5 : bv_unsigned (rw rho5 101%positive) = res1).
      { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 101%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
      assert (Hres0 : res1 = 0).
      { pose proof (holds_fact rho5 _ _ HF5 Keq) as X. unfold vRes1 in X. cbn [holds eval branch_taken] in X. unfold bv_eqb in X.
        rewrite lit_unsigned in X. change (0 mod 2 ^ 64) with 0 in X. destruct (Z.eqb_spec (bv_unsigned (rw rho5 101%positive)) 0) as [E0|NE]; [lia|].
        exfalso. apply X. reflexivity. }
      assert (HlenF' : len = Z.of_nat (length F)) by (pose proof BS1_len; unfold res1 in *; lia).
      eapply (etriple_conseq (P := fun w => exists rho6, SPA segs (JR (KcR (len + res1)) rho0 P0 k nd_R) Hc1 rho6 tp w));
        [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (q_cleanup (KcR (len + res1)) rho0 P0 k Lcl1 H1a H1b H1c Hc1 rho5 tp w (KcG_ok _ _) Xa Kn Kset Ks eq_refl eq_refl Xc Kobjs Knb KX KQ HW5 (P0RD1_SH g len want F) HS)
          as (rho6 & _ & HS6). exists rho6. exact HS6. }
      apply etriple_ex. intros rho6. unfold KcR. replace (len + res1) with len by lia. apply (Hclose HlenF').
Qed.
End ReadStep1.

Section CopyStep1.
Variables (g : nat) (len want res k : Z) (rho0 : valuation).
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
S8eVg;Vlen;Vwant;VF;A4").
Hypothesis Hg : (g <= 10)%nat.
Hypothesis Hlen : 4 <= len.
Hypothesis Hres : 1 <= res <= want.
Hypothesis Hw : want <= 65536.
Hypothesis Hlw : ltac2:(tb__ "0|0|
S4aS4bVlen;Vwant;A2S8bVg;A1A2").
Hypothesis HlenF : ltac2:(tb__ "0|0|
S4aS4bVlen;Vres;A2S4dS32S46Q8A1VF;A2A1A2").
Hypothesis Hk : 0 <= k.
Hypothesis Hloop : ltac2:(tb__ "0|1|
S4cS4bVlen;Vres;A2M0S8bVg;A1A2S3S2dS46Q40A1A1S70S45S6bS45S56S57G0A1R2S91Vg;G0VF;A3Vk;S75A5Sd5R2R1A5VQ;A3Ftp';Frho';F_;").
Hypothesis Hgrow : ltac2:(tb__ "0|3|
S3eS0S4bVlen;Vres;A2M0S8bVg;A1M1A3S4cG1S4eZ2Z1aA2A2S3S2dS46Q40M2A1A1S3eS0S47G2S4R2P65A2A2Vres;A3S70S45S6bS45S56S57G0A1Vrho0;VP0;Vk;S75A5Se1R3R2A5VQ;A3F_;Ftp';Frho';F_;F_;").
Hypothesis Href : ltac2:(tb__ "0|2|
S3eS0S4bVlen;Vres;A2M0S8bVg;A1M1A3S4aS4eZ2Z1aA2G1A2S3S2dS46Q40A1A1S70S45S6bS45S56S57G0A1Vrho0;VP0;Vk;S75A5Sd8R2R1A5VQ;A3Ftp';Frho';F_;F_;").

Let pcallR := pure_callJ_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA.

Lemma step_cp1 : ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S3eS0S47G0S4R2P65A2A2Vres;A3S70S45S6bS45S56S57S4bVlen;Vres;A2A1Vrho0;VP0;Vk;S75A5Se8R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HR. pose proof (cap_le g Hg) as HC.
  destruct cp1_site as (Sp1 & Sp2 & Sp3 & Sp4 & Sp5 & Hn5 & Hset5 & Hs5 & Sp7 & Hn7 & Hset7 & Hs7 & Hcv & HC1 & HnodeC & HfB & Hf4096 & HfC & HnxC).
  destruct (node_okb_sound _ _ HnodeC) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct cp1_call as (Hs15 & Hs16 & Hs19 & Hs52 & Hs18 & HPosts & HnodeT & HLVC).
  destruct (node_okb_sound _ _ HnodeT) as (T1 & T2 & T3 & T4 & T5 & T6).

  apply (triple_pre _ _ _ (fun w HS => SPA_JR_facts _ _ _ _ _ _ _ _ _ HS)). intros ((HP0 & HP49) & Hav & HFQ).
  pose proof HP0 as (Q24 & Q42o & Q41o & Q45 & QSH).
  pose proof Q42o as Q42. rewrite <- (U_agree rho0 rho 42%positive Hav ltac:(cbv; reflexivity)) in Q42.
  pose proof Q41o as Q41. rewrite <- (U_agree rho0 rho 41%positive Hav ltac:(cbv; reflexivity)) in Q41. unfold U in Q42, Q41.
  pose proof (U_SPUle_lit_r rho _ vB ATOPHI HFQ HfB ltac:(unfold ATOPHI; lia)) as HvB.
  assert (HvL : bv_unsigned (eval rho vLen) <= 2 ^ 26) by (change (eval rho vLen) with (rw rho 42%positive); lia).
  assert (HvR : bv_unsigned (eval rho vRes1) <= 65536) by (change (eval rho vRes1) with (rw rho 101%positive); lia).

  eapply (etriple_conseq (P := SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) C_cp1 rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs _ rho Q1 0 (SLit (-2288)) S1cp tp w Sp1 HS) as HS1.
    pose proof (SPA_split segs _ rho (mkAX S1cp (ax_X Q1) (ax_base Q1)) 0 (SLit (-2368)) S2cp tp w Sp2 HS1) as HS2.
    pose proof (SPA_split segs _ rho (mkAX S2cp (ax_X Q1) (ax_base Q1)) _ (SLit 4) S3cp tp w Sp3 HS2) as HS3.
    pose proof (SPA_split segs _ rho (mkAX S3cp (ax_X Q1) (ax_base Q1)) _ vLen S4cp tp w Sp4 HS3) as HS4.
    pose proof (SPA_split segs _ rho (mkAX S4cp (ax_X Q1) (ax_base Q1)) _ (add vLen vRes1) S5cp tp w Sp5 HS4) as HS5.
    destruct (dst_ranges rho vRes1 HvB HvL HvR) as (_ & DR1 & _ & _ & DR2 & DR3).
    pose proof (SPA_reslice segs _ rho (mkAX S5cp (ax_X Q1) (ax_base Q1)) _ _ (O_dstC vRes1) tp w Hn5 eq_refl eq_refl eq_refl eq_refl
                  ltac:(cbn [ax_S]; rewrite Hset5; exact Hs5) DR1 DR2 DR3 HS5) as HS6.
    cbn [ax_S ax_setS ax_X ax_base] in HS6. rewrite Hset5 in HS6.
    pose proof (SPA_split segs _ rho (mkAX S6cp (ax_X Q1) (ax_base Q1)) _ (add (SLit RS) vRes1) S7cp tp w Sp7 HS6) as HS7.
    destruct (rds_ranges rho rdsb vRes1 [] (U_rdsb rho) HvR) as (_ & RR1 & _ & _ & RR2 & RR3).
    pose proof (SPA_reslice segs _ rho (mkAX S7cp (ax_X Q1) (ax_base Q1)) _ _ (O_rdsC vRes1 []) tp w Hn7 eq_refl eq_refl eq_refl eq_refl
                  ltac:(cbn [ax_S]; rewrite Hset7; exact Hs7) RR1 RR2 RR3 HS7) as HS8.
    cbn [ax_S ax_setS ax_X ax_base] in HS8. rewrite Hset7 in HS8.
    unfold carve_chk in Hcv. apply andb_prop in Hcv as [Hcv Hb6]. apply andb_prop in Hcv as [Hw6 Hc6]. apply sv_eqb_sound in Hb6.
    rewrite <- HC1.
    pose proof (carveR rho0 P0 k (P0RD1_SH g len want F) (KcR (len + res)) nd_R (mkAX S8cp (ax_X Q1) (ax_base Q1)) rho tp w N_mc (ss_next S8cp) HS8 Hw6 (Pos.leb_refl _) Hb6 Hc6) as HS9.
    exact HS9. }

  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
               JR (KcR (len + res)) rho0 P0 k nd_R rho t tr md /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 15 16 /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 19 52).
  assert (HstJp : stableA segs NF Jp).
  { intros r r' t tr md md' Hag Hme (HJ & C1 & C2). unfold Jp. split; [|split].
    - destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_R Ai kc rho rho t tr md md' (Pos.le_refl _) nd_R_NF (agree_below_refl _ _) Hme HJi).
    - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in C1 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C1.
    - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in C2 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C2. }
  apply (pcallR (KcR (len + res)) (KcR (len + res)) C_cp1 PreC s_cp1 R_cp1 PostsC rho tp nd_R Jp Jp Q (KcG_ok _ _)).
  - intros rho6 tp6. apply (memcpy_icpt_sum_ex Jp rho6 tp6 HstJp).
    + intros r t tr md (_ & C1 & _). exact C1.
    + intros r t tr md (_ & _ & C2). exact C2.
  - exact fr_cp1.
  - exact cc_cp1.
  - exact M1.
  - exact M3.
  - exact M4.
  -
    intros tr ms md Hsm HJ. unfold Jp. split; [exact HJ|].
    assert (HnzB : tnz rho (vB, vCap)).
    { unfold tnz, vB. cbn [fst eval]. pose proof (holds_fact rho _ _ HFQ Hf4096) as X. unfold vB in X. cbn [holds eval] in X.
      rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
    split.
    + apply band_free_clsZ. rewrite !rw_call'. rewrite Hs15, Hs16.
      exact (JR_tv_band_free _ _ _ _ nd_R rho tp tr md (vB, vCap) HJ ltac:(left; reflexivity) HnzB).
    + apply rds_clsZ; rewrite !rw_call'; [rewrite Hs19; apply U_RS | rewrite Hs52, U_lit; change (65536 mod M64v) with 65536; lia].
  - intros rhoL tr' md' (HJ & _). exact HJ.
  -
    intros Lf rho3 HinL Hag3. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S C_cp1)) (import_postA s_cp1 PreC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.P_icpt C_cp1 R_cp1)) with (T_after PreC C_cp1 s_cp1 R_cp1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.P_icpt).
    rewrite T_cp1_eq.
    assert (HR3 : bv_unsigned (rw rho3 101%positive) = res).
    { destruct Hag3 as (Hv3 & _ & _). rewrite <- (Hv3 101%positive ltac:(rewrite HnxC; apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
    pose proof run_C1 as RC1. rewrite HLVC in RC1.
    eapply JR_run; [exact Hk | exact RC1 | exact T2 | exact T1 | exact T3 |].
    intros L5 rho5 HinL5 Hag5.
    assert (HR5 : bv_unsigned (rw rho5 101%positive) = res).
    { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 101%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR3. }

    apply (triple_pre _ _ _ (fun w HS => SPA_JR_facts _ _ _ _ _ _ _ _ _ HS)). intros (_ & Hav5 & HF5).
    pose proof Q42o as R42. rewrite <- (U_agree rho0 rho5 42%positive Hav5 ltac:(cbv; reflexivity)) in R42.
    pose proof Q41o as R41. rewrite <- (U_agree rho0 rho5 41%positive Hav5 ltac:(cbv; reflexivity)) in R41.
    unfold U in R42, R41.
    pose proof (U_len1 rho5 len res HR5 R42 ltac:(lia) ltac:(lia) ltac:(lia)) as UL1.
    assert (HvB5 : forall Lx, existsb (sprop_eqb (SPUle vB (SLit ATOPHI))) (ss_facts (ax_S Lx)) = true -> Lx = la_state L5 -> bv_unsigned (eval rho5 vB) <= ATOPHI).
    { intros Lx Hx ->. exact (U_SPUle_lit_r rho5 _ vB ATOPHI HF5 Hx ltac:(unfold ATOPHI; lia)). }
    assert (HvL5 : bv_unsigned (eval rho5 vLen) <= 2 ^ 26) by (change (eval rho5 vLen) with (rw rho5 42%positive); lia).
    assert (HvR5 : bv_unsigned (eval rho5 vRes1) <= 65536) by (change (eval rho5 vRes1) with (rw rho5 101%positive); lia).
    destruct HinL5 as [<-|[<-|[<-|[]]]]; cbn [la_state] in *.
    +
      destruct cp1_ref as (HB & Feq & Fsrl). pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfB5).
      pose proof (proj1 (holds_beq _ _ _) (holds_fact rho5 _ _ HF5 Feq)) as W1. rewrite UL1 in W1. change (eval rho5 vCap) with (rw rho5 41%positive) in W1. rewrite R41 in W1.
      pose proof (proj1 (holds_bne _ _ _) (holds_fact rho5 _ _ HF5 Fsrl)) as W2. rewrite U_srl26, UL1, U_lit in W2. change (0 mod M64v) with 0 in W2.
      assert (Hge : 2 ^ 26 <= cap g) by (destruct (Z_lt_le_dec (len + res) (2 ^ 26)) as [Hlt|Hge]; [rewrite Z.div_small in W2 by lia; lia | lia]).
      eapply (etriple_conseq (P := fun w => exists rho6, SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) Lref rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (bk_cleanup _ rho0 P0 k _ _ _ _ _ _ rho5 tp w (KcG_ok _ _) HB (HvB5 _ HfB5 eq_refl) HvL5 HvR5 (P0RD1_SH g len want F) HS) as (rho6 & _ & HS6).
        exists rho6. exact HS6. }
      apply etriple_ex. intros rho6. exact (Href W1 Hge rho6 tp).
    +
      destruct cp1_grow as (HB & Feq & Fsrl). pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfB5).
      pose proof (proj1 (holds_beq _ _ _) (holds_fact rho5 _ _ HF5 Feq)) as W1. rewrite UL1 in W1. change (eval rho5 vCap) with (rw rho5 41%positive) in W1. rewrite R41 in W1.
      pose proof (proj1 (holds_nbne _ _ _) (holds_fact rho5 _ _ HF5 Fsrl)) as W2. rewrite U_srl26, UL1, U_lit in W2. change (0 mod M64v) with 0 in W2.
      assert (Hlt : cap g < 2 ^ 26).
      { destruct (Z_lt_le_dec (len + res) (2 ^ 26)) as [Hlt|Hge]; [lia|].
        exfalso. pose proof (Z.div_le_mono (2 ^ 26) (len + res) (2 ^ 26) ltac:(lia) Hge) as D. rewrite Z.div_same in D by lia. lia. }
      eapply (etriple_conseq (P := fun w => exists rho6, bv_unsigned (rw rho6 101%positive) = res /\ SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) E_m rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (bk_cleanup _ rho0 P0 k _ _ _ _ _ _ rho5 tp w (KcG_ok _ _) HB (HvB5 _ HfB5 eq_refl) HvL5 HvR5 (P0RD1_SH g len want F) HS) as (rho6 & Hv6 & HS6).
        exists rho6. split; [rewrite Hv6; exact HR5 | exact HS6]. }
      apply etriple_ex. intros rho6. apply (triple_pre _ _ (bv_unsigned (rw rho6 101%positive) = res)); [intros w [H _]; exact H | intros HR6].
      eapply (etriple_conseq (P := SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) E_m rho6 tp)); [intros w [_ HS]; exact HS | intros w' Hw'; exact Hw' |].
      exact (Hgrow W1 Hlt rho6 tp HR6).
    +
      destruct cp1_back as (HB & Fne & EF & Ffb & KnodeU & K24 & K30 & K42 & K41 & K40 & K45 & Ktv & Kbud).
      pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KnodeB & HfB5).
      destruct (node_okb_sound _ _ KnodeU) as (U1 & U2 & U3 & U4 & U5 & U6).
      pose proof (proj1 (holds_nbeq _ _ _) (holds_fact rho5 _ _ HF5 Fne)) as W1. rewrite UL1 in W1. change (eval rho5 vCap) with (rw rho5 41%positive) in W1. rewrite R41 in W1.
      assert (Hlt : len + res < cap g) by lia.
      eapply (etriple_conseq (P := fun w => exists rho6, bv_unsigned (rw rho6 101%positive) = res /\ bv_unsigned (rw rho6 42%positive) = len /\ bv_unsigned (rw rho6 41%positive) = cap g
                                                  /\ SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) (ax_add_facts F_bk1 B1u) rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (bk_cleanup _ rho0 P0 k _ _ _ _ _ _ rho5 tp w (KcG_ok _ _) HB (HvB5 _ HfB5 eq_refl) HvL5 HvR5 (P0RD1_SH g len want F) HS) as (rho6 & Hv6 & HS6).
        exists rho6. split; [rewrite Hv6; exact HR5|]. split; [rewrite Hv6; exact R42|]. split; [rewrite Hv6; exact R41|].
        change (ax_add_facts F_bk1 B1u) with (ax_with_facts B1u (F_bk1 ++ ss_facts (ax_S B1u))).
        apply (SPA_refacts_JA segs); [exact HS6 | exact U4 |].
        intros tr md HJ HF6. apply Forall_app. split; [|exact HF6]. rewrite EF.
        pose proof (U_len1 rho6 len res ltac:(rewrite Hv6; exact HR5) ltac:(rewrite Hv6; exact R42) ltac:(lia) ltac:(lia) ltac:(lia)) as UL6.
        assert (C6 : bv_unsigned (eval rho6 vCap) = cap g) by (change (eval rho6 vCap) with (rw rho6 41%positive); rewrite Hv6; exact R41).
        constructor; [|constructor; [|constructor]]; cbn [holds]; unfold add; rewrite ?U_add, ?UL6, ?U_lit, ?C6, <- ?M64v_eq; [rewrite (Z.mod_small 1), Z.mod_small by lia; lia | lia]. }
      apply etriple_ex. intros rho6.
      apply (triple_pre _ _ (bv_unsigned (rw rho6 101%positive) = res /\ bv_unsigned (rw rho6 42%positive) = len /\ bv_unsigned (rw rho6 41%positive) = cap g)); [intros w (H1 & H2 & H3 & _); auto | intros (HR6 & R42' & R41')].
      eapply (etriple_conseq (P := SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) (ax_add_facts F_bk1 B1u) rho6 tp)); [intros w (_ & _ & _ & HS); exact HS | intros w' Hw'; exact Hw' |].
      eapply (etriple_conseq (P := SPA segs (JR (KcR (len + res)) (rho_sub rho6 s_bk1) (P0R1 g (len + res) F) k nd_R) R1c (rho_sub rho6 s_bk1) tp));
        [intros w HS | intros w' Hw'; exact Hw' | apply (Hloop Hlt)].
      apply (JR_reorigin (KcR (len + res)) rho0 P0 (P0R1 g (len + res) F) k (ax_add_facts F_bk1 B1u) R1c s_bk1 nd_R nd_R rho6 tp w ent_bk1 K24 K30 U1 U3 Ktv eq_refl Kbud eq_refl); [|exact HS].
      intros Ai kc HF6 HP0' Hav6 Hkept Hkc HJi.
      unfold P0R1, U. cbn [rho_sub rw]. rewrite K24, K42, K41, K45. cbn [eval].
      destruct Hav6 as [Hv6 _].
      rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)), <- (Hv6 45%positive ltac:(cbv; reflexivity)).
      split; [exact Q24|]. split; [exact (U_len1 rho6 len res HR6 R42' ltac:(lia) ltac:(lia) ltac:(lia))|]. split; [exact R41'|]. split; [exact Q45|].
      change (rm (rho_sub rho6 s_bk1)) with (rm rho6).
      exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ (P0RD1_SHR g len want) HJi).
Qed.
End CopyStep1.

Section Head1.
Variables (g : nat) (len k : Z) (rho0 : valuation).
Let P0 := P0R1 g len F.
Hypothesis Hg : (g <= 10)%nat.
Hypothesis Hlen : ltac2:(tb__ "0|0|
S3fS4aZ4Vlen;A2S4cVlen;S8bVg;A1A2A2").
Hypothesis HlenF : len <= Z.of_nat (length F).
Hypothesis Hk : 0 <= k.
Hypothesis Hrd : ltac2:(tb__ "0|0|
S0S3S2dS46Q40A1A1S3fS4aZ1R3A2S4aR3Z10000A2A2S4aS4bVlen;R4A2S8bVg;A1A2S70S45S6bS45S56S57Vlen;A1R4S8eVg;Vlen;R5VF;A4Vk;S75A5SedR4R3A5VQ;A3F_;F_;Ftp';Frho';Fwant;").

Lemma step_head1 : ltac2:(tb__ "0|0|
S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5Sd5Vrho0;R1A5VQ;A3Ftp;").
Proof.
  intros tp. pose proof (cap_le g Hg) as HC.
  destruct head1_facts as (Hnode & HLVR & Ea & Eb & Na & Nb & A24 & A30 & A49 & A42 & A41 & A45 & B24 & B30 & B49 & B42 & B41 & B45 & Atv & Btv & Abud & Bbud & Fa1 & Fb1).
  destruct (node_okb_sound _ _ Hnode) as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (node_okb_sound _ _ Na) as (Na1 & Na2 & Na3 & _). destruct (node_okb_sound _ _ Nb) as (Nb1 & Nb2 & Nb3 & _).
  pose proof run_R1 as RR. rewrite HLVR in RR.
  eapply JR_run; [exact Hk | exact RR | exact N2 | exact N1 | exact N3 |].
  intros L rho1 HinL Hag1.
  apply (triple_pre _ _ _ (fun w HS => SPA_JR_facts _ _ _ _ _ _ _ _ _ HS)). intros ((Q24 & Q42 & Q41 & Q45 & QSH) & Hav & HF).
  rewrite <- (U_agree rho0 rho1 42%positive Hav ltac:(cbv; reflexivity)) in Q42.
  rewrite <- (U_agree rho0 rho1 41%positive Hav ltac:(cbv; reflexivity)) in Q41. unfold U in Q42, Q41.
  assert (USUB : bv_unsigned (eval rho1 (SAlu ALU_SUB vCap vLen)) = cap g - len).
  { rewrite U_sub. change (eval rho1 vCap) with (rw rho1 41%positive). change (eval rho1 vLen) with (rw rho1 42%positive).
    rewrite Q41, Q42, <- M64v_eq. apply Z.mod_small. lia. }
  destruct HinL as [<-|[<-|[]]]; cbn [la_state] in *.
  -
    pose proof (proj1 (holds_bltu _ _ _) (holds_fact rho1 _ _ HF Fa1)) as W1. rewrite USUB, U_lit in W1. change (65536 mod M64v) with 65536 in W1.
    eapply (etriple_conseq (P := SPA segs (JR (KcR len) (rho_sub rho1 s_RDa) (P0RD1 g len (cap g - len) F) k nd_R) RD1 (rho_sub rho1 s_RDa) tp));
      [intros w HS | intros w' Hw'; exact Hw' | apply (Hrd (cap g - len)); lia].
    apply (JR_reorigin (KcR len) rho0 P0 (P0RD1 g len (cap g - len) F) k Ra1 RD1 s_RDa nd_R nd_R rho1 tp w Ea A24 A30 Na1 Na3 Atv eq_refl Abud eq_refl); [|exact HS].
    intros Ai kc HF6 HP0 Hav6 Hkept Hkc HJi. destruct HP0 as (P24 & P42 & P41 & P45 & PSH).
    unfold P0RD1, P0R1, U. cbn [rho_sub rw]. rewrite A24, A49, A42, A41, A45. cbn [eval]. destruct Hav6 as [Hv6 _].
    rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)), <- (Hv6 42%positive ltac:(cbv; reflexivity)), <- (Hv6 41%positive ltac:(cbv; reflexivity)), <- (Hv6 45%positive ltac:(cbv; reflexivity)).
    unfold U in P24, P42, P41, P45. split; [|exact USUB]. repeat (split; [assumption|]).
    change (rm (rho_sub rho1 s_RDa)) with (rm rho1). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ (P0R1_SHR g len) HJi).
  -
    pose proof (proj1 (holds_nbltu _ _ _) (holds_fact rho1 _ _ HF Fb1)) as W1. rewrite USUB, U_lit in W1. change (65536 mod M64v) with 65536 in W1.
    eapply (etriple_conseq (P := SPA segs (JR (KcR len) (rho_sub rho1 s_RDb) (P0RD1 g len 65536 F) k nd_R) RD1 (rho_sub rho1 s_RDb) tp));
      [intros w HS | intros w' Hw'; exact Hw' | apply (Hrd 65536); lia].
    apply (JR_reorigin (KcR len) rho0 P0 (P0RD1 g len 65536 F) k Rb1 RD1 s_RDb nd_R nd_R rho1 tp w Eb B24 B30 Nb1 Nb3 Btv eq_refl Bbud eq_refl); [|exact HS].
    intros Ai kc HF6 HP0 Hav6 Hkept Hkc HJi. destruct HP0 as (P24 & P42 & P41 & P45 & PSH).
    unfold P0RD1, P0R1, U. cbn [rho_sub rw]. rewrite B24, B49, B42, B41, B45. cbn [eval]. destruct Hav6 as [Hv6 _].
    rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)), <- (Hv6 42%positive ltac:(cbv; reflexivity)), <- (Hv6 41%positive ltac:(cbv; reflexivity)), <- (Hv6 45%positive ltac:(cbv; reflexivity)).
    unfold U in P24, P42, P41, P45. split; [|rewrite lit_unsigned; reflexivity]. repeat (split; [assumption|]).
    change (rm (rho_sub rho1 s_RDb)) with (rm rho1). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ (P0R1_SHR g len) HJi).
Qed.
End Head1.

Section GrowPre.
Variables (g : nat) (len want res k : Z) (rho0 : valuation).
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
S8eVg;Vlen;Vwant;VF;A4").
Hypothesis Hg : (g <= 10)%nat.
Hypothesis Hlen : 0 <= len.
Hypothesis Hres : 0 <= res.
Hypothesis Hlc : ltac2:(tb__ "0|0|
S3eS0S4bVlen;Vres;A2S8bVg;A1A3").
Hypothesis Hl26 : cap g < 2 ^ 26.
Hypothesis Hk : 0 <= k.
Hypothesis HG : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57S8bVg;A1A1R2S93Vg;VF;A2Vk;S75A5Sd7R2R1A5VQ;A3Ftp';Frho';").

Lemma step_grow_pre : ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S3eS0S47G0S4R2P65A2A2Vres;A3S70S45S6bS45S56S57S4bVlen;Vres;A2A1Vrho0;VP0;Vk;S75A5Se1R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HR. pose proof (cap_le g Hg) as HC. pose proof (cap_lt26 g Hg ltac:(lia)) as HC25.
  destruct grow_pre_facts as (Gw & Gnx & Gd & Gset & Gfb & Gent & GnE & GnG & G24 & G30 & G41 & G45 & Gtv & Gbud).
  destruct (node_okb_sound _ _ GnE) as (E1 & E2 & E3 & E4 & E5 & E6).
  apply (triple_pre _ _ _ (fun w HS => SPA_JR_facts _ _ _ _ _ _ _ _ _ HS)). intros (((Q24 & Q42 & Q41 & Q45 & QSH) & _) & Hav & HF).
  rewrite <- (U_agree rho0 rho 42%positive Hav ltac:(cbv; reflexivity)) in Q42.
  rewrite <- (U_agree rho0 rho 41%positive Hav ltac:(cbv; reflexivity)) in Q41. unfold U in Q42, Q41.
  pose proof (U_len1 rho len res HR Q42 ltac:(lia) ltac:(lia) ltac:(lia)) as UL1.
  assert (EQW : eval rho len1 = eval rho vCap).
  { apply bv_eq. rewrite UL1. change (eval rho vCap) with (rw rho 41%positive). rewrite Q41. exact Hlc. }
  unfold len1, vRes1, vLen, vCap, add in EQW. cbn [eval] in EQW.

  eapply (etriple_conseq (P := SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) E_mGf rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { assert (HS1 : SPA segs (JR (KcR (len + res)) rho0 P0 k nd_R) (ax_setS E_m (ax_S E_mG)) rho tp w).
    { apply (SPA_restate segs _ rho E_m (ax_S E_mG) tp w _ [] Gw Gd Gnx); [| constructor | exact HS].
      unfold diffs_ok. repeat constructor. all: unfold len1, two_cap, vRes1, vLen, vCap, add; cbn [fst snd eval]; rewrite ?EQW; reflexivity. }
    rewrite Gset in HS1. unfold E_mGf, ax_add_facts.
    change (ax_setS E_mG (add_facts [SPUle vCap (SLit (2 ^ 25))] (ax_S E_mG))) with (ax_with_facts E_mG ([SPUle vCap (SLit (2 ^ 25))] ++ ss_facts (ax_S E_mG))).
    apply (SPA_refacts_JA segs); [exact HS1 | | ].
    - rewrite forallb_app, Gfb. cbn [andb]. exact (swf_facts _ Gw).
    - intros tr md HJ HF'. apply Forall_app. split; [|exact HF']. constructor; [|constructor].
      cbn [holds eval]. change (eval rho vCap) with (rw rho 41%positive). rewrite Q41, lit_unsigned. change ((2 ^ 25) mod 2 ^ 64) with (2 ^ 25). exact HC25. }
  eapply (etriple_conseq (P := SPA segs (JR (KcR (cap g)) (rho_sub rho s_G) (P0G g F) k nd_R) G_cut (rho_sub rho s_G) tp));
    [intros w HS | intros w' Hw'; exact Hw' | apply HG].
  rewrite <- Hlc.
  apply (JR_reorigin (KcR (len + res)) rho0 P0 (P0G g F) k E_mGf G_cut s_G nd_R nd_R rho tp w Gent G24 G30 E1 E3 Gtv eq_refl Gbud eq_refl); [|exact HS].
  intros Ai kc HF6 HP0 Hav6 Hkept Hkc HJi.
  unfold P0G, U. cbn [rho_sub rw]. rewrite G24, G41, G45. cbn [eval]. destruct Hav6 as [Hv6 _].
  rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)), <- (Hv6 45%positive ltac:(cbv; reflexivity)).
  split; [exact Q24|]. split; [exact Q41|]. split; [exact Q45|].
  change (rm (rho_sub rho s_G)) with (rm rho). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ (P0RD1_SHR g len want) HJi).
Qed.
End GrowPre.

Section Grow.
Variables (g : nat) (k : Z) (rho0 : valuation).
Let capg := cap g.
Let P0 := P0G g F.
Hypothesis Hg : (g <= 10)%nat.
Hypothesis Hc26 : capg < 2 ^ 26.
Hypothesis HcF : capg <= Z.of_nat (length F).
Hypothesis Hk : 2 * KU <= k.

Hypothesis HkK : ltac2:(tb__ "0|0|
S4aS4fSb3S4bS105Z2A2A2Vk;A2").

Hypothesis Hnext : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Vcapg;A1R2S91S3bVg;A1Vcapg;VF;A3S50Vk;S4fZ2Sb3A2A2S75A5Sd5R2R1A5VQ;A3Ftp';Frho';").

Lemma cap_S : ltac2:(tb__ "0|0|
S3eS0S8bS3bVg;A1A1S4fZ2S8bVg;A1A2A3").
Proof. unfold cap. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.

Lemma cap_half : capg <= 2 ^ 25.
Proof.
  unfold capg, cap in *. destruct (Nat.eq_dec g 10) as [->|Hne]; [exfalso; cbn in Hc26; lia|].
  assert (HP : 2 ^ Z.of_nat g <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in HP. lia.
Qed.

Lemma step_grow : ltac2:(tb__ "0|0|
S2dS46Q40A1A1S70S45S6bS45S56S57Vcapg;A1Vrho0;VP0;Vk;S75A5Sd7Vrho0;R1A5VQ;A3Ftp;").
Proof.
  intros tp. pose proof (cap_le g Hg) as HC. unfold KU in Hk.
  destruct grow_malloc_facts as (Mn & McT & Ms12 & Msb & Mimp & MvN & Mbb & Mpay & Mro & Mxr & MTn & MTo & MnN & MnO & MLn & MLo & Mf1 & Mf2).
  destruct (node_okb_sound _ _ Mn) as (N1 & N2 & N3 & N4 & N5 & N6).

  eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF (KcR capg) rho0 P0 [] [] (BXk (k - KU)) PA nd_Rk) G_cut rho0 tp));
    [intros w HS; apply (SPA_JR_takeK (KcR capg) rho0 P0 k KU [(vB, vCap)] bd_R G_cut rho0 tp w ltac:(unfold KU; lia) eq_refl HS) | intros w' Hw'; exact Hw' |].
  apply etriple_factsA. intros HF0.
  apply (triple_pre _ _ (P0 rho0)); [intros w HS; exact (proj1 (SPA_JR_facts (KcR capg) rho0 P0 (k - KU) nd_Rk G_cut rho0 tp w HS)) | intros HP00].

  apply (malloc_callA_ex_S segs AE_A AInv CST XGL ALA HCST HXGL NF (KcR capg) rho0 P0 [] [] (BXk (k - KU)) PA (KcG_ok _ _) PA [] UStopLe G_cut s_mG R_mG rho0 tp nd_Rk bd_mid
           Q malloc_shape_nil MSX fr_mG (call_checkPA_drop1 _ _ _ _ _ _ cc_mG) McT N1 N3 Mbb Msb Mimp).
  - apply payA_of_bud_pay. cbn [nd_bd nd_Rk]. rewrite Ms12. exact Mpay.
  -
    intros A A' HPA0 HC0. eapply HPAm; [|exact HPA0|exact HC0].
    rewrite Ms12. unfold uval. destruct HP00 as (_ & Q41 & _). unfold U in Q41.
    rewrite U_sll1; change (eval rho0 vCap) with (rw rho0 41%positive); rewrite Q41; unfold capg in *; lia.
  -
    intros A kc _ Hkc HB. rewrite Ms12. unfold uval. destruct HP00 as (_ & Q41 & _). unfold U in Q41. pose proof cap_half as CH.
    rewrite U_sll1; change (eval rho0 vCap) with (rw rho0 41%positive); rewrite Q41; [| unfold capg in *; lia].
    cbn [nd_bd nd_am nd_Rk] in HB. exact (room_G A kc rho0 k _ Q41 CH HkK Hkc HB).
  - reflexivity.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  -
    apply (site_ok_drv AInv CST XGL ALA HCSTdrv rho0 P0 nd_Rk G_cut s_mG R_mG rho0 None None _ N6 Mro Mxr).
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0' Hav HN HD HZ HM. destruct HP0' as (_ & Q41 & _). unfold U in Q41. split; [|exact I].
      rewrite Ms12. unfold uval. rewrite U_sll1; change (eval rho0 vCap) with (rw rho0 41%positive); rewrite Q41; unfold capg in *; lia.
  -
    intros rho' tp'. unfold PreM in MTo. rewrite MTo. cbn [nd_tv nd_fr nd_am nd_Rk]. rewrite MvN, Ms12. fold two_cap. fold nd_G1.
    destruct grow_mc_facts as (Cfb & CnEf & Cs1 & Cs2 & Cs3 & Ccv & CC & CnC & C15 & C19 & C16 & C52 & CT & CnT & CLV & C4096 & CnE & CnO & CkN & CkB & CPosts).
    destruct (node_okb_sound _ _ CnO) as (O1 & O2 & O3 & _).
    pose proof (proj2 run_G) as RG. rewrite MLo in RG.
    eapply JR_run; [unfold KU; lia | exact RG | exact O2 | exact O1 | exact O3 |].
    intros L rho2 [<-|[]] Hag2. cbn [la_state].
    apply etriple_factsA. intros HF2.

    destruct (node_okb_sound _ _ CnE) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    eapply (etriple_conseq (P := SPA segs (JR (KcR capg) rho0 P0 (k - KU) nd_G1) E_mcf rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { unfold E_mcf, ax_add_facts. change (ax_setS E_mc (add_facts mc_kfacts (ax_S E_mc))) with (ax_with_facts E_mc (mc_kfacts ++ ss_facts (ax_S E_mc))).
      apply (SPA_refacts_JA segs); [exact HS | rewrite forallb_app, Cfb; exact Q4 |].
      intros tr md HJ HF. apply Forall_app. split; [|exact HF].
      assert (HvN : 4096 <= bv_unsigned (rw rho2 vN')).
      { pose proof (holds_fact rho2 _ _ HF C4096) as X. cbn [holds eval] in X. rewrite lit_unsigned in X. change (4096 mod 2 ^ 64) with 4096 in X. exact X. }
      assert (Htnz : tnz rho2 (SVar vN', two_cap)) by (unfold tnz; cbn [fst eval]; lia).
      pose proof (JA_tv_facts segs AInv CST XGL NF (KcR capg) rho0 P0 [] [] (BXk (k - KU)) PA ALA nd_G1 rho2 tp' tr md (SVar vN', two_cap) eq_refl HJ ltac:(left; reflexivity) Htnz) as TF.
      unfold tv_factsA in TF. cbn [fst snd bx2] in TF.
      inversion TF as [| ? ? T1 TF2]; subst. inversion TF2 as [| ? ? _ TF3]; subst. inversion TF3 as [| ? ? T3 TF4]; subst.
      inversion TF4 as [| ? ? _ TF5]; subst. inversion TF5 as [| ? ? _ TF6]; subst. inversion TF6 as [| ? ? T6 TF7]; subst.
      inversion TF7 as [| ? ? T7 TF8]; subst. inversion TF8 as [| ? ? T8 _]; subst.
      pose proof (SPA_JR_facts _ _ _ _ _ _ _ _ _ HS) as ((_ & P41 & _) & Hav2 & _).
      rewrite <- (U_agree rho0 rho2 41%positive Hav2 ltac:(cbv; reflexivity)) in P41. unfold U in P41.
      assert (U2C : bv_unsigned (eval rho2 two_cap) = 2 * capg).
      { unfold two_cap. rewrite U_sll1; change (eval rho2 vCap) with (rw rho2 41%positive); rewrite P41; unfold capg in *; lia. }
      unfold mc_kfacts. constructor; [|constructor; [|constructor; [exact T1 | constructor; [exact T3 | constructor; [exact T6 | constructor; [exact T8 | constructor; [exact T7 | constructor]]]]]]]; cbn [holds].
      - rewrite U2C. change (eval rho2 vCap) with (rw rho2 41%positive). rewrite P41. unfold capg in *; lia.
      - unfold add. rewrite U_add, U2C, U_lit. change (eval rho2 vCap) with (rw rho2 41%positive). rewrite P41, <- M64v_eq. change (1 mod 2 ^ 64) with 1.
        rewrite Z.mod_small; unfold capg in *; lia. }
    clear HF2. apply etriple_factsA. intros HF2.

    unfold carve_chk in Ccv. apply andb_prop in Ccv as [Ccv Cb3]. apply andb_prop in Ccv as [Cw3 Cc3]. apply sv_eqb_sound in Cb3.
    eapply (etriple_conseq (P := SPA segs (JR (KcR capg) rho0 P0 (k - KU) nd_G1) C_mc rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { apply (SPA_split segs _ rho2 E_mcf 0 (SLit (-2160)) _ tp' w Cs1) in HS. change (ax_setS E_mcf (ax_S A1_mc)) with A1_mc in HS.
      apply (SPA_split segs _ rho2 A1_mc 0 (SLit (-2240)) _ tp' w Cs2) in HS. change (ax_setS A1_mc (ax_S A2_mc)) with A2_mc in HS.
      apply (SPA_split segs _ rho2 A2_mc _ vCap _ tp' w Cs3) in HS. change (ax_setS A2_mc (ax_S A3_mc)) with A3_mc in HS.
      rewrite <- CC. apply (carveR rho0 P0 (k - KU) (P0G_SH g F) (KcR capg) nd_G1 A3_mc rho2 tp' w N_mc (ss_next (ax_S A3_mc)) HS Cw3 (Pos.leb_refl _) Cb3 Cc3). }
    destruct (node_okb_sound _ _ CnC) as (D1 & D2 & D3 & D4 & D5 & D6).

    set (Jmc := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
                  JR (KcR capg) rho0 P0 (k - KU) nd_G1 rho2 t tr md /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 15 16 /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 19 52).
    assert (Jmc_stable : stableA segs NF Jmc).
    { intros r r' t tr md md' Hag Hme (HJ & H15 & H19). split; [|split].
      - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
        eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk (k - KU)) PA (KcG_ok _ _) ALA (ss_next (ax_S C_mc)) nd_G1 Ai kc rho2 rho2 t tr md md' ltac:(apply Pos.leb_le; exact D1) D3 (agree_below_refl _ _) Hme HJ').
      - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in H15 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact H15.
      - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in H19 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact H19. }
    apply (pure_callJ_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk (k - KU)) PA (KcR capg) (KcR capg) C_mc PreMC s_mc R_mc PostsMC rho2 tp' nd_G1
             Jmc Jmc Q (KcG_ok _ _)).
    + intros rho3 tp3. apply (memcpy_icpt_hdr_sum_ex Jmc rho3 tp3 Jmc_stable).
      * intros r t tr md (_ & H15 & _). exact H15.
      * intros r t tr md (_ & _ & H19). exact H19.
    + exact fr_mc.
    + exact cc_mc.
    + exact D1.
    + exact D3.
    + exact D4.
    +   intros tr ms md Hsm HJ. split; [exact HJ|]. pose proof (smatchA_facts segs _ _ _ _ Hsm) as HFc.
      assert (HnzN : tnz rho2 (SVar vN', two_cap)).
      { unfold tnz. cbn [fst eval]. pose proof (holds_fact rho2 _ _ HFc CkN) as X. cbn [holds eval] in X. rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
      assert (HnzB : tnz rho2 (vB, vCap)).
      { unfold tnz, vB. cbn [fst eval]. pose proof (holds_fact rho2 _ _ HFc CkB) as X. unfold vB in X. cbn [holds eval] in X. rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
      split; apply band_free_clsZ; rewrite !rw_call'.
      * rewrite C15, C16. exact (JR_tv_band_free _ _ _ _ nd_G1 rho2 tp' tr md (SVar vN', two_cap) HJ ltac:(left; reflexivity) HnzN).
      * rewrite C19, C52. exact (JR_tv_band_free _ _ _ _ nd_G1 rho2 tp' tr md (vB, vCap) HJ ltac:(right; left; reflexivity) HnzB).
    +   intros rhoL tr' md' (HJ' & _). exact HJ'.
    +
      intros L rho3 HinL Hag3. rewrite CPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state].
      change (ax_add_facts (ss_facts (ax_S C_mc)) (import_postA s_mc PreMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr.P_icpt C_mc R_mc)) with (T_after PreMC C_mc s_mc R_mc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr.P_icpt).
      rewrite CT. destruct (node_okb_sound _ _ CnT) as (T1 & T2 & T3 & _).
      pose proof run_mc as RM. rewrite CLV in RM.
      eapply JR_run; [unfold KU; lia | exact RM | exact T2 | exact T1 | exact T3 |].
      intros Lf rho4 [<-|[]] Hag4. cbn [la_state].
      destruct grow_free_facts as (Gxf & GF2 & GX & GF2o & Gnb2 & GCf & GnCf & GcT & Gs12 & Gs13 & Gbb & Gpay & Gro & Gxr & G4096 & GTf & GnTf & GLV & GnBg
                                   & Gs24 & Gs30 & Gs40 & Gs41 & Gs42 & Gs45 & Gtv & Gbud).
      destruct (node_okb_sound _ _ GnCf) as (F1' & F2' & F3' & F4' & F5' & F6').

      eapply (etriple_conseq (P := fun w => exists rho5, SPA segs (JR (KcR capg) rho0 P0 (k - KU) nd_G1) C_f rho5 tp' w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct w as [tr [ms md]].
        apply (SPA_axforms segs _ XF_f rho4 E_f F1 tp' _ Gxf) in HS.
        apply (SPA_x_sub segs _ rho4 F1 X_G tp' _ (xrs_inclb_sound _ _ GX)) in HS. rewrite GF2 in HS.
        pose proof (uncarveR rho0 P0 (k - KU) (P0G_SH g F) (KcR capg) nd_G1 F2 rho4 tp' tr ms md (objs38 F2) N_mc (KcG_ok _ _) GF2o N_mc_un eq_refl Gnb2 HS) as HS2.
        rewrite GCf in HS2. eexists. exact HS2. }
      apply etriple_ex. intros rho5.

      eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF (KcR capg) rho0 P0 [] [] (BXk (k - KU - KU)) PA nd_G1k) C_f rho5 tp'));
        [intros w HS; apply (SPA_JR_takeK (KcR capg) rho0 P0 (k - KU) KU [(SVar vN', two_cap); (vB, vCap)] bd_mid C_f rho5 tp' w ltac:(unfold KU; lia) eq_refl HS) | intros w' Hw'; exact Hw' |].
      apply etriple_factsA. intros HF5.
      apply (triple_pre _ _ (P0 rho0 /\ agree_vals NF rho0 rho5));
        [intros w HS; destruct (SPA_JR_facts (KcR capg) rho0 P0 (k - KU - KU) nd_G1k C_f rho5 tp' w HS) as (X1 & X2 & _); split; [exact X1 | exact X2] | intros [HP05 Hav5]].
      assert (HvB : 4096 <= bv_unsigned (rw rho5 40%positive)).
      { pose proof (holds_fact rho5 _ _ HF5 G4096) as X. cbn [holds eval] in X. rewrite lit_unsigned in X. change (4096 mod 2 ^ 64) with 4096 in X. exact X. }
      apply (free_callA_ex segs AE_A AInv CST XGL ALA HCST HXGL NF (KcR capg) rho0 P0 [] [] (BXk (k - KU - KU)) PA (KcG_ok _ _) [] UStopLe C_f s_f R_f rho5 tp' nd_G1k 1%nat (vB, vCap) bd_mid
               Q free_shape_nil ACX fr_f cc_f GcT F1' F3' Gbb eq_refl).
      * apply payA_of_bud_pay. cbn [nd_bd nd_G1k]. exact Gpay.
      *
        apply HPAf. pose proof (cap_le g Hg). unfold capg in *. lia.
      *
        apply (site_ok_drv AInv CST XGL ALA HCSTdrv rho0 P0 nd_G1k C_f s_f R_f rho5 (Some 1%nat) (Some (uval rho5 (wsub_get s_f 12))) _ F6' Gro Gxr).
        -- intros Ai HF' HN HZ. exists (vB, vCap). split; [reflexivity|]. rewrite Gs12. unfold tnz, tvv, uval, vB, vCap. cbn [fst snd eval]. split; [lia | reflexivity].
        -- intros Ai ms HF' HP0' Hav HN HD HZ HM. rewrite Gs12, Gs13. unfold tnz, tvv, uval, vB, vCap. cbn [fst snd eval]. split; [lia|]. split; [reflexivity | exact I].
      *
        intros rho6 tp6. unfold PreF, PostF in GTf. rewrite GTf. cbn [nd_tv nd_fr nd_am nd_G1k remove_nth]. fold nd_G2.
        destruct (node_okb_sound _ _ GnTf) as (U1 & U2 & U3 & _).
        pose proof run_f as RF. rewrite GLV in RF.
        eapply JR_run; [unfold KU; lia | exact RF | exact U2 | exact U1 | exact U3 |].
        intros Lf2 rho7 [<-|[]] Hag7. cbn [la_state].
        destruct (node_okb_sound _ _ GnBg) as (B1' & B2' & B3' & _).
        eapply (etriple_conseq (P := SPA segs (JR (KcR capg) rho0 P0 (k - KU - KU) nd_G2) Bg rho7 tp6)); [intros w HS; exact (SPA_axforms segs _ [AXRebase 0] rho7 Lg Bg tp6 w Bg_eq HS) | intros w' Hw'; exact Hw' |].
        replace (k - KU - KU) with (k - 2 * KU) by lia.
        eapply (etriple_conseq (P := SPA segs (JR (KcR capg) (rho_sub rho7 s_bkG) (P0R1 (S g) capg F) (k - 2 * KU) nd_R) R1c (rho_sub rho7 s_bkG) tp6));
          [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
        apply (JR_reorigin (KcR capg) rho0 P0 (P0R1 (S g) capg F) (k - 2 * KU) Bg R1c s_bkG nd_G2 nd_R rho7 tp6 w ent_bkG Gs24 Gs30 B1' B3' Gtv eq_refl Gbud eq_refl); [|exact HS].
        intros Ai kc HF7 HP0 Hav7 Hkept Hkc HJi. destruct HP0 as (P24 & P41 & P45 & PSH).
        unfold P0R1, U. cbn [rho_sub rw]. rewrite Gs24, Gs42, Gs41, Gs45. destruct Hav7 as [Hv7 _].
        assert (E24 : rw rho7 24%positive = rw rho0 24%positive) by (symmetry; apply (Hv7 24%positive); cbv; reflexivity).
        assert (E41 : rw rho7 41%positive = rw rho0 41%positive) by (symmetry; apply (Hv7 41%positive); cbv; reflexivity).
        assert (E45 : rw rho7 45%positive = rw rho0 45%positive) by (symmetry; apply (Hv7 45%positive); cbv; reflexivity).
        unfold U in P24, P41, P45. pose proof (cap_le g Hg) as HCg.
        split; [|split; [|split; [|split]]].
        -- cbn [eval]. rewrite E24. exact P24.
        -- change (eval rho7 vCap) with (rw rho7 41%positive). rewrite E41. exact P41.
        -- rewrite cap_S. unfold two_cap. rewrite U_sll1; change (eval rho7 vCap) with (rw rho7 41%positive); rewrite E41, P41; unfold capg in *; lia.
        -- unfold vH. cbn [eval ext_low]. change (bv_extract 0 32 (rw rho7 45%positive)) with (low32 (rw rho7 45%positive)).
           rewrite (sext64_32_mod (low32 (rw rho7 45%positive)) 32) by lia. rewrite low32_umod, Z.mod_mod by lia. rewrite E45. exact P45.
        -- change (rm (rho_sub rho7 s_bkG)) with (rm rho7). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ (P0G_SHR g) HJi).
Qed.
End Grow.

Section CloseStep.
Variables (len k : Z) (rho0 : valuation) (P0 : valuation -> Prop) (nd : ndesc).
Variables (Hc Ecl : axst) (leaves : list leafA).
Hypothesis Hk : 0 <= k.
Hypothesis HnodeH : ltac2:(tb__ "0|0|
S3eS31S77VHc;Vnd;A2S30A3").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S3eS34S2dS82A1M0A1S87S45U28Se0VHc;S30A5S33G0S37S82S89VEcl;S14dA2S2fS82A1A3A2A3").
Hypothesis Hi : ltac2:(tb__ "0|0|
S3eS34S13fA1S14eS45S24S81VEcl;A1A1A2S33S13fS144A2A3").
Hypothesis H17 : ltac2:(tb__ "0|0|
S3eS5S22S81VEcl;A1Z11A2S8Z39A1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S3eS5S22S81VEcl;A1ZaA2S8Z3A1A3").
Hypothesis HnodeE : ltac2:(tb__ "0|0|
S3eS31S77VEcl;Vnd;A2S30A3").
Hypothesis HnodeA : ltac2:(tb__ "0|0|
S3eS31S77S153VEcl;S8Z0A1A2Vnd;A2S30A3").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S3eS34S2dS82A1M0A1S87S45U78Se0S153VEcl;S8Z0A1A2S30A5S33G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|0|
S82ScbS82R1Vleaves;A3S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;Vnd;A5S85R4A1R2R1A5VQ;A3Ftp';Frho';F_;FLf;").

Lemma step_close : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;Vnd;A5VHc;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp.
  destruct (node_okb_sound _ _ HnodeH) as (N1 & N2 & N3 & _). destruct (node_okb_sound _ _ HnodeE) as (E1 & E2 & E3 & _).
  destruct (node_okb_sound _ _ HnodeA) as (A1 & A2 & A3 & _).
  eapply JR_run; [exact Hk | exact Hrun1 | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  eapply etriple_seq with (R := SPA segs (JR KcC rho0 P0 k nd) (A_after Ecl (SLit 0)) rho1 tp).
  - change (A_after Ecl (SLit 0)) with (closeA' Ecl).
    apply (etriple_closeA segs Ecl rho1 tp Hi H17 H10).
    + apply JR_stable; [apply KcG_ok | exact Hk | apply Pos.leb_le; exact E1 | exact E3].
    + intros tr md HJ. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & _). rewrite Hfds. eexists. apply HFDS3.
    + intros tr md HJ. unfold close_md'. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & _).
      eapply JR_refds; [|exact HJ]. rewrite Hfds. apply HFDC.
  - eapply JR_run; [exact Hk | exact Hrun2 | exact A2 | exact A1 | exact A3 |].
    intros Lf rho2 Hin Hag2. apply (Hleaves Lf Hin).
Qed.
End CloseStep.

Section Close1.
Variables (len k : Z) (rho0 : valuation) (P0 : valuation -> Prop).
Hypothesis Hk : 0 <= k.
Hypothesis Hsh : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;S75A5SddR2R1A5VQ;A3Ftp';Frho';").
Hypothesis Hov : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;S75A5SdcR2R1A5VQ;A3Ftp';Frho';").
Hypothesis Htr : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;S75A5SdeR2R1A5VQ;A3Ftp';Frho';").
Lemma step_close1 : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5Se3R2R1A5VQ;A3Ftp;Frho;").
Proof.
  destruct close1_facts as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  destruct rd1_close as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KnodeQ & _).
  pose proof (proj1 run_c) as R1. rewrite C1 in R1. pose proof (proj1 run_h) as R2. rewrite C7 in R2.
  apply (step_close len k rho0 P0 nd_R Hc1 E_cl1 _ Hk KnodeQ R1 C2 C3 C4 C5 C6 R2).
  intros Lf [<-|[<-|[<-|[]]]] rho' tp'; cbn [la_state]; [apply Hsh | apply Hov | apply Htr].
Qed.
End Close1.

Section Loop1.

Variable kT : Z.
Hypothesis HkT : 0 <= kT.
Hypothesis HkTK : ltac2:(tb__ "0|0|
S4aS4fSb3S105A2VkT;A2").

Hypothesis HTtr : ltac2:(tb__ "0|0|
S36S0S0S0S3Sc5R5UaA2S3fS4aZ4R5A2S4cR5S8bR6A1A2A2S3eS0R6S4dS32S46Q8A1VF;A2A1A3S3fS4aZ1R6A2S4aR6Z10000A2A2S4aVkT;R6A2S3S2dS46Q40A1A1S70S45S6bS45S56S58R8S8eRcRbRaVF;A4R9S75A5SdeR2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;F_;Frho0;Fk;Fwant;Flen;Fg;").
Hypothesis HTsh : ltac2:(tb__ "0|0|
S36S0S0S0S3Sc5R5UaA2S3fS4aZ4R5A2S4cR5S8bR6A1A2A2S3eS0R6S4dS32S46Q8A1VF;A2A1A3S3fS4aZ1R6A2S4aR6Z10000A2A2S4aVkT;R6A2S3S2dS46Q40A1A1S70S45S6bS45S56S58R8S8eRcRbRaVF;A4R9S75A5SddR2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;F_;Frho0;Fk;Fwant;Flen;Fg;").
Hypothesis HTov : ltac2:(tb__ "0|0|
S36S0S0S0S3Sc5R5UaA2S3fS4aZ4R5A2S4cR5S8bR6A1A2A2S3eS0R6S4dS32S46Q8A1VF;A2A1A3S3fS4aZ1R6A2S4aR6Z10000A2A2S4aVkT;R6A2S3S2dS46Q40A1A1S70S45S6bS45S56S58R8S8eRcRbRaVF;A4R9S75A5SdcR2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;F_;Frho0;Fk;Fwant;Flen;Fg;").
Hypothesis HTref : ltac2:(tb__ "0|0|
S36S0S0S0S0S3Sc5R6UaA2S4aZ4R6A2S3fS4aZ1R5A2S4aR5R6A2A2S4aR7Z10000A2S3eS0S4bR9R7A2S8bRaA1A3S4aS4eZ2Z1aA2S8bRbA1A2S4aS4bRbR9A2S4dS32S46Q8A1VF;A2A1A2S4aVkT;R9A2S3S2dS46Q40A1A1S70S45S6bS45S56S57S4bRfRdA2A1RbS8eR10RfReVF;A4RcS75A5Sd8R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;F_;F_;F_;F_;Frho0;Fk;Fres;Fwant;Flen;Fg;").

Lemma loop1_core : ltac2:(tb__ "0|0|
S36S36S3eS36S15aR1R2A2UaA3S36S0S0S3S2dS46Q40A1A1S4cS50S8bR7A1R4A2S4dR5A1A2S3fS4aZ4R5A2S4cR5S8bR8A1A2A2S4aR6S4dS32S46Q8A1VF;A2A1A2S4aS4bVkT;S4fS4fZ2Sb3A2S4dRbA1A2A2R6A2S70S45S6bS45S56S57R8A1R6S91RbR8VF;A3R7S75A5Sd5R6R5A5VQ;A3F_;F_;F_;F_;Ftp;Frho0;Fk;Flen;Fm;F_;Fg;Fdg;").
Proof.
  induction dg as [|dg IHg]; intros g Hgd m; induction m as [|m IHm]; intros len k rho0 tp Hm Hlen HlenF Hk; try lia.
  all: assert (Hg : (g <= 10)%nat) by lia; unfold KU in *.
  all: apply (step_head1 g len k rho0 Hg Hlen ltac:(lia)).
  all: intros want rho' tp' Hw Hlw; apply (step_rd1 g len want k rho' Hg ltac:(lia) Hlw Hw HlenF ltac:(lia)).

  - intros Hres rho'' tp'' HR. apply (step_cp1 g len want (res1 len want) k rho' Hg ltac:(lia) ltac:(unfold res1 in *; lia) ltac:(lia) Hlw ltac:(lia)); [| | |exact HR].
    + intros Hlt rho3 tp3. apply (IHm (len + res1 len want) k rho3 tp3); unfold res1, KU in *; lia.
    + intros Hlc H26. exfalso. assert (g = 10)%nat by lia. subst g. unfold cap in H26. change (2 ^ Z.of_nat 10) with 1024 in H26. lia.
    + intros Hlc H26 rho3 tp3. apply (HTref g len want (res1 len want) k rho' Hg ltac:(lia) ltac:(unfold res1 in *; lia) ltac:(lia) Hlc H26 ltac:(unfold res1 in *; lia) ltac:(lia)).
  - intros HlF rho'' tp''. apply (step_close1 len k rho' (P0RD1 g len want F) ltac:(lia)); intros rho3 tp3;
      [apply (HTsh g len want k rho' Hg Hlen HlF Hw ltac:(lia)) | apply (HTov g len want k rho' Hg Hlen HlF Hw ltac:(lia)) | apply (HTtr g len want k rho' Hg Hlen HlF Hw ltac:(lia))].

  - intros Hres rho'' tp'' HR. apply (step_cp1 g len want (res1 len want) k rho' Hg ltac:(lia) ltac:(unfold res1 in *; lia) ltac:(lia) Hlw ltac:(lia)); [| | |exact HR].
    + intros Hlt rho3 tp3. apply (IHm (len + res1 len want) k rho3 tp3); unfold res1, KU in *; lia.
    + intros Hlc H26 rho3 tp3 HR3. apply (step_grow_pre g len want (res1 len want) k rho' Hg ltac:(lia) ltac:(unfold res1 in *; lia) Hlc H26); [|exact HR3].
      intros rho4 tp4. apply (step_grow g k rho4 Hg H26 ltac:(unfold res1 in *; lia) ltac:(unfold KU; lia) ltac:(unfold KU in *; lia)).
      * intros rho5 tp5. pose proof (cap_S g) as CS. pose proof (cap_le g Hg) as CL.
        apply (IHg (S g) ltac:(lia) (S (Z.to_nat (cap (S g)))) (cap g) (k - 2 * KU) rho5 tp5); unfold res1, KU in *; rewrite ?CS in *; try lia.
    + intros Hlc H26 rho3 tp3. apply (HTref g len want (res1 len want) k rho' Hg ltac:(lia) ltac:(unfold res1 in *; lia) ltac:(lia) Hlc H26 ltac:(unfold res1 in *; lia) ltac:(lia)).
  - intros HlF rho'' tp''. apply (step_close1 len k rho' (P0RD1 g len want F) ltac:(lia)); intros rho3 tp3;
      [apply (HTsh g len want k rho' Hg Hlen HlF Hw ltac:(lia)) | apply (HTov g len want k rho' Hg Hlen HlF Hw ltac:(lia)) | apply (HTtr g len want k rho' Hg Hlen HlF Hw ltac:(lia))].
Qed.

Theorem loop1 : ltac2:(tb__ "0|0|
S36S0S0S3S2dS46Q40A1A1Sc5R5UaA2S3fS4aZ4R5A2S4cR5S8bR6A1A2A2S4aR6S4dS32S46Q8A1VF;A2A1A2S4aS4bVkT;S4fS4fZ2Sb3A2S50ZaS4dR8A1A2A2A2R6A2S70S45S6bS45S56S57R8A1R6S91R9R8VF;A3R7S75A5Sd5R6R5A5VQ;A3F_;F_;F_;F_;Ftp;Frho0;Fk;Flen;Fg;").
Proof.
  intros g len k rho0 tp Hg Hlen HlenF Hk.
  apply (loop1_core (10 - g)%nat g ltac:(lia) (S (Z.to_nat (cap g - len))) len k rho0 tp); try lia.
  rewrite Nat2Z.inj_sub by lia. change (Z.of_nat 10) with 10. lia.
Qed.

Theorem grow0 : ltac2:(tb__ "0|1|
S0S3S2dS46Q40A1A1S4aZ10000S4dS32S46Q8A1VF;A2A1A2S4aS4bS4bVkT;S4fS4fZ2Sb3A2ZaA2A2Sb3A2S4bR4Sb3A2A2S4aS4bVkT;Sb3A2R5A2S70S45S6bS45S56S57S8bU0M0A1A1R5S93G0VF;A2R6S75A5Sd7R5R4A5VQ;A3F_;F_;F_;Ftp;Frho0;Fk;").
Proof.
  intros k rho0 tp HF Hk1 Hk2. unfold KU in *.
  apply (step_grow 0 k rho0 ltac:(lia) ltac:(cbv; reflexivity) ltac:(change (cap 0) with 65536; lia) ltac:(unfold KU; lia) ltac:(unfold KU in *; lia)).
  - intros rho5 tp5. pose proof (cap_S 0) as CS.
    apply (loop1 1%nat (cap 0) (k - 2 * KU) rho5 tp5 ltac:(lia)); unfold KU in *; rewrite ?CS; change (cap 0) with 65536 in *; try lia.
Qed.
End Loop1.

Definition MDT (md : Model) : Prop := ltac2:(tb__ "0|0|
S3fS3eS2dS2eS46Q40A1S5eA2A1S63Vmd;A1VFDC;A3VMDX;Vmd;A1A2").

Section HandT.
Variables (g : nat) (len want k : Z) (rho0 : valuation).
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
S8eVg;Vlen;Vwant;VF;A4").
Hypothesis Hg : (g <= 10)%nat.
Hypothesis Hlen : ltac2:(tb__ "0|0|
S3fS4aZ4Vlen;A2S4cVlen;S8bVg;A1A2A2").
Hypothesis HlenF : len = Z.of_nat (length F).
Hypothesis Hk : ltac2:(tb__ "0|0|
S4aS4fSb3S105A2Vk;A2").

Hypothesis HT : ltac2:(tb__ "0|1|
S3fS4aS4bZ6S103VF;A1A2S4dS32S46Q8A1VF;A2A1M0A2S4cG0S131A2A2S3S3S2dS46Q40A1A1S70S45S6bS45SfcVAInv;VCST;VXGL;R3VF;VT0;S5bVPA;U0S107AaS106R2R1A5VQ;A3Ftp;Frho;FrhoT;F_;").

Lemma step_T : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;S75A5SdeR2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. pose proof (cap_le g Hg) as HC.
  destruct tr_facts as (Tn & T101 & Tlt & Tdiff & Twf & Tnx & Tset & Tfb & TnK & T24 & T30 & T40 & T41 & T42 & T43 & T44 & T45 & T46 & Ttv & Tbud & TndT).
  destruct (node_okb_sound _ _ Tn) as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (node_okb_sound _ _ TnK) as (K1 & K2 & K3 & K4 & K5 & K6).
  apply etriple_factsA. intros HF.
  apply (triple_pre _ _ (P0 rho0 /\ agree_vals NF rho0 rho));
    [intros w HS; destruct (SPA_JR_facts KcC rho0 P0 k nd_R Ltr rho tp w HS) as (X1 & X2 & _); split; [exact X1 | exact X2] | intros [HP0 Hav]].
  destruct HP0 as [(Q24 & Q42 & Q41 & Q45 & QSH) Q49].
  rewrite <- (U_agree rho0 rho 24%positive Hav ltac:(cbv; reflexivity)) in Q24.
  rewrite <- (U_agree rho0 rho 42%positive Hav ltac:(cbv; reflexivity)) in Q42.
  rewrite <- (U_agree rho0 rho 41%positive Hav ltac:(cbv; reflexivity)) in Q41.
  rewrite <- (U_agree rho0 rho 45%positive Hav ltac:(cbv; reflexivity)) in Q45. unfold U in Q24, Q42, Q41, Q45.
  pose proof (clen_of_range F) as HCR.
  assert (H101 : bv_unsigned (rw rho 101%positive) = 0).
  { pose proof (holds_fact rho _ _ HF T101) as X. unfold vRes1 in X. cbn [holds eval branch_taken] in X. unfold bv_eqb in X.
    rewrite lit_unsigned in X. change (0 mod 2 ^ 64) with 0 in X.
    destruct (Z.eqb_spec (bv_unsigned (rw rho 101%positive)) 0) as [E0|NE]; [exact E0|]. exfalso. apply X. reflexivity. }
  assert (Hcl : clen_of F + 6 <= len).
  { pose proof (holds_fact rho _ _ HF Tlt) as X. unfold vLen in X. cbn [holds branch_taken] in X. unfold bv_ltu in X.
    change (eval rho (SVar 42%positive)) with (rw rho 42%positive) in X.
    assert (E2 : bv_unsigned (eval rho (add clen_x (SLit 6))) = clen_of F + 6).
    { unfold add. rewrite U_add, U_lit, (U_clen_x F rho Q45). unfold M64v. rewrite (Z.mod_small 6) by lia. apply Z.mod_small. lia. }
    rewrite Q42, E2 in X. destruct (Z.ltb_spec len (clen_of F + 6)); [exfalso; apply X; reflexivity | lia]. }

  eapply (etriple_conseq (P := SPA segs (JR KcC rho0 P0 k nd_R) LtrK rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { assert (HS1 : SPA segs (JR KcC rho0 P0 k nd_R) (ax_setS Ltr (ax_S LtrR)) rho tp w).
    { apply (SPA_restate segs _ rho Ltr (ax_S LtrR) tp w _ [] Twf Tdiff Tnx); [| constructor | exact HS].
      unfold diffs_ok. repeat constructor. unfold vRes1. cbn [fst snd eval]. apply bv_eq. rewrite H101, lit_unsigned. reflexivity. }
    rewrite Tset in HS1. unfold LtrK, ax_add_facts.
    change (ax_setS LtrR (add_facts [SPUle clen_x (SLit 32767)] (ax_S LtrR))) with (ax_with_facts LtrR ([SPUle clen_x (SLit 32767)] ++ ss_facts (ax_S LtrR))).
    apply (SPA_refacts_JA segs); [exact HS1 | rewrite forallb_app, Tfb; exact (swf_facts _ Twf) |].
    intros tr md _ HF'. apply Forall_app. split; [|exact HF']. constructor; [|constructor].
    cbn [holds]. rewrite (U_clen_x F rho Q45), U_lit. unfold M64v. rewrite Z.mod_small by lia. lia. }

  eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF KcC rho0 P0 [] [] BX0 PA nd_RT) LtrK rho tp)); [intros w [Hsm (Ai & kc & HJ)] | intros w' Hw'; exact Hw' |].
  { split; [exact Hsm|]. exists Ai, kc.
    apply (JAi_rebud KcC rho0 P0 (BXk k) BX0 nd_R bd_T Ai kc rho tp); [reflexivity | cbn; lia | cbn; lia | reflexivity | | exact HJ].
    intros V Km Kf HB. cbn [nd_bd nd_am nd_R] in HB |- *. destruct HB as (_ & _ & _ & _ & _ & _ & Hnn & _).
    unfold bxa, BXk, BX0, bd_T, bd_R, bsumV, bsumK, bival, BIc. cbn [fst snd bx2 lfval bi_f bi_c bi_v bi_k aval uval]. unfold uval.
    change (eval rho vCap) with (rw rho 41%positive). rewrite Q41.
    assert (HVT : 0 <= V_T /\ 0 <= KU * K_T).
    { unfold V_T, K_T, KU, NCALLS, CV, MAX_INPUT, CV0, CK_DIV, CK0. split; cbv; discriminate. }
    split; [unfold bd_nn; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold bival; cbn [lfval bi_f bi_c]; lia|].
    unfold VR in *. pose proof (proj2 HC). lia. }

  eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF KcC (rho_sub rho s_T) (P0T F) [] [] BX0 PA nd_T) S_T (rho_sub rho s_T) tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { rewrite TndT. change BX0 with (BXk 0).
    apply (JR_reorigin KcC rho0 P0 (P0T F) 0 LtrK S_T s_T nd_RT (NDA tv_T [] bd_T ANone) rho tp w ent_T T24 T30 K1 K3 Ttv eq_refl Tbud eq_refl); [|exact HS].
    intros Ai kc HF6 _ _ Hkept Hkc HJi. unfold P0T, P0f_T. cbn [rho_sub rw]. rewrite T24, T42, T43, T44, T45, T46.
    split; [| change (rm (rho_sub rho s_T)) with (rm rho); exact (proj1 (SHR_now _ _ _ _ _ _ _ _ _ _ _ (P0RD1_SHR g len want) HJi))].
    split; [cbn [eval]; exact Q24|].
    split; [cbn [eval]; rewrite Q42; exact HlenF|].
    split; [exact (U_clen_x F rho Q45)|].
    split; [rewrite (U_plen_x F rho Q45 len H101 Q42 Hcl ltac:(lia)); lia|].
    split; [cbn [eval]; exact Q45|].
    exact (U_flg_x F rho Q45). }

  eapply (etriple_conseq (P := SPA segs (JT AInv CST XGL (rho_sub rho s_T) F T0 MDT PA 0%nat nd_T) S_T (rho_sub rho s_T) tp)); [intros w HS | intros w' Hw'; exact Hw' | apply HT; unfold MAX_INPUT; lia].
  unfold JT.
  apply (SPA_JA_Kc AInv CST XGL NF KcC _ (rho_sub rho s_T) (P0T F) [] [] _ PA nd_T S_T (rho_sub rho s_T) tp w); [|exact HS].
  intros tr md (Htr & Hfds & HX). split; [split; [exact Hfds | exact HX] | exact Htr].
Qed.
End HandT.

Lemma MSGB_oom : MSGB 0x14d77 19 = msg_oom. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma MSGB_short : MSGB 0x21441 31 = msg_short. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma MSGB_overrun : MSGB 0x1609e 31 = msg_overrun. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma Kw_JR : ltac2:(tb__ "0|3|
S2dS2eS46Q40A1M0S5eA2A1S2dS5cA1M1S3S3OF_;S0S96S3S0S0S36S3S2dG0A1M2G1S5dSc4S3G2G1S5dS56S59R12R11A2R10RfReRdRcR3R2R1A9Lmd;Ltr;Lt;L_;R7R6R5R4R3R2R1A8S56S59RfS35S5cReSc3R8R7R6A3A3A2RdRcRbRaR9R4R3R2A9F_;Fmd';Ftr';Ft;FrhoL;Fn;Flen;Fmsg;Frho1;Fnd;Fk;FP0;Frho0;Fevs;Ffds;").
Proof.
  intros fds evs rho0 P0 k nd rho1 msg len n rhoL t tr' md' (tr0 & HJ & ->).
  destruct HJ as (Ai & kc & Hav & (Htr & Hfd & HX) & REST). exists Ai, kc. split; [exact Hav|]. split; [|exact REST].
  split; [rewrite Htr, <- app_assoc; reflexivity|]. split; [exact Hfd | exact HX].
Qed.

Lemma is_prefix_firstn_app : forall (A : Type) (l m : list A) n, is_prefix (firstn n l) (l ++ m).
Proof.
  intros A l m n. revert l. induction n as [|n IH]; intros [|x l]; cbn; try exact I; try apply is_prefix_nil.
  split; [reflexivity | apply IH].
Qed.

Lemma splitA_eq : ltac2:(tb__ "0|0|
S36S5S80SfS3eS34SfA1S164S81R2A1R4R3A3S33SfR1A2A3S3eS80S15fR5R4R3A3S83R3R2A2A3F_;FS';FA;Fmid;Fi;").
Proof. intros i mid A S' H. unfold splitA, optS. rewrite H. reflexivity. Qed.
Lemma mergeA_eq : ltac2:(tb__ "0|0|
S36S80SfS3eS34SfA1S163S81R2A1R3A2S33SfR1A2A3S3eS80S15eR4R3A2S83R3R2A2A3F_;FS';FA;Fi;").
Proof. intros i A S' H. unfold mergeA, optS. rewrite H. reflexivity. Qed.

Section TailFree.
Variables (tb tl : sv) (bd : list bitem) (msg len blkB blkL : Z).
Variables (Lx Ex Cx Tx Ux Vx Wx Fx CFx TFx Xx CXx : axst) (sx sF : wsub) (Rx RF : list sobj).
Variable msgB : list byte.
Hypothesis Hfw : ltac2:(tb__ "0|0|
ScbS2eS0S0A2S38S0S0Vmsg;Vlen;A4S139A3").
Hypothesis Hmsg : ltac2:(tb__ "0|0|
S3eS2dS46Q8A1A1S13aVmsg;Vlen;A2VmsgB;A3").

Hypothesis Hblk : ltac2:(tb__ "0|0|
S0S3fS4aS112VblkB;A1R1A2S4cR1S112S4bVblkB;VblkL;A2A1A2A2S90R2A1F_;Fz;").
Variables (P0 : valuation -> Prop) (k : Z) (rho0 : valuation).
Hypothesis HP0 : ltac2:(tb__ "0|0|
S3VP0;R1A1S8cR2A1F_;Fr;").
Hypothesis Hk : KU <= k.
Hypothesis Hbdw : bd_wpos bd = true.
Hypothesis TFF : ltac2:(tb__ "0|0|
S149Vtb;Vtl;Vbd;Vmsg;Vlen;VblkB;VblkL;VLx;VEx;VCx;VTx;VUx;VVx;VWx;VFx;VCFx;VTFx;VXx;VCXx;Vsx;VsF;VRx;VRF;A17").

Hypothesis HS : ltac2:(tb__ "0|0|
S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafS46Q8A1S5cS60Sc2A1VmsgB;A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;").

Let HP0SH : forall r, P0 r -> SH0 r := fun r H => proj1 (HP0 r H).

Lemma tailF_exit : ltac2:(tb__ "0|2|
S2dS5cA1M0S3eG0R1SafS46Q8A1S5cS60Sc2A1VmsgB;A4A3S3S2dS46Q40A1A1S70S45S6bS45S97VAInv;VCST;VXGL;S8aS59VFDC;R4A2Vrho0;VP0;S2fS2eS0S0A2M1A1S2fS2eG1S0A2A1Sf8Sa5S148AcVTFx;R2R1A5VQ;A3Ftp;Frho;F_;Fevs;").
Proof.
  intros evs Eevs rho5 tp5.
  destruct TFF as (Fn & Frun & Fx4 & Fsp & Cw3 & Cc3 & Cb3 & Fpub & FC & FnC & Ffr & Fcc & FT & Fsel & FS1o & FnbS1 & FU & FV & Fx4v & FW & FnW & FrunW
                   & Fxi & FCF & FnCF & FfrF & FccF & FcT & Fbb & Fs12 & Fs13 & Fpay & Fro & Fxr & Fnz & FTF & FnTF & FrunX
                   & FE1 & Fselx & Fmrg & Fspx & Fimg & Xw3 & Xc3 & Xb3 & Fx4x & Fxix & FCX & FnCX & Ffrx & Fccx).
  destruct (node_okb_sound _ _ FnTF) as (U1 & U2 & U3 & U4 & U5 & U6).
  eapply (JK_erun AInv CST XGL ALA (KcG FDC evs) (KcG_ok _ _) rho0 P0 PTrue nd_X); [exact FrunX | exact U2 | exact U1 | exact U3 |].
  intros Lz rho6 [<-|[]] Hag6. cbn [la_state].

  eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF (KcG FDC evs) rho0 P0 [] [] BX0 PTrue nd_X) CXx rho6 tp5)); [intros w HSP | intros w' Hw'; exact Hw' |].
  { apply (SPA_axforms segs _ _ rho6 Xx (E1x Xx) tp5 _ FE1) in HSP.
    apply (AxXform.SPA_select segs _ rho6 (E1x Xx) _ tp5 w Fselx) in HSP. change (ax_setS (E1x Xx) _) with (TB0 Xx) in HSP.
    apply (SPA_merge segs _ rho6 (TB0 Xx) 0 _ tp5 w Fmrg) in HSP. rewrite <- (mergeA_eq 0 (TB0 Xx) _ Fmrg) in HSP. change (mergeA 0 (TB0 Xx)) with (TB0' Xx) in HSP.
    apply (SPA_split segs _ rho6 (TB0' Xx) 0 (SLit (-1072)) _ tp5 w Fspx) in HSP. rewrite <- (splitA_eq 0 (SLit (-1072)) (TB0' Xx) _ Fspx) in HSP.
    apply (SPA_x_sub segs _ rho6 _ [] tp5 w ltac:(intros rr Hrr; destruct Hrr)) in HSP. change (ax_setX (splitA 0 (SLit (-1072)) (TB0' Xx)) []) with (TB1 Xx) in HSP.
    apply (SPA_img_cell segs _ rho6 (TB1 Xx) _ _ _ _ tp5 w Fimg) in HSP. change (ax_setS (TB1 Xx) _) with (TB2 Xx) in HSP.
    assert (HS3 : SPA segs (JA AInv CST XGL NF (KcG FDC evs) rho0 P0 [] [] BX0 PTrue nd_X) (TB3 Xx) rho6 tp5 w).
    { exact (JA_carve AInv CST XGL ALA NF rho0 P0 [] [] BX0 PTrue KV_T (HKV_K AInv CST XGL ALA HCSTdrv HLPP KcC rho0 P0 HP0SH PA PTrue) HKVrng_T KP_T
               (HKP_K AInv CST XGL HCSTdrv KcC rho0 P0 HP0SH PA PTrue) (KcG FDC evs) nd_X (TB2 Xx) rho6 tp5 w N_exR (ss_next (ax_S (TB2 Xx))) HSP Xw3 (Pos.leb_refl _) Xb3 Xc3). }
    clear HSP.
    apply (SPA_x4set _ rho6 (TB3 Xx) (SLit TP) tp5 w Fx4x) in HS3. change (x4set (SLit TP) (TB3 Xx)) with (TB4 Xx) in HS3.
    apply (SPA_x_sub segs _ rho6 (TB4 Xx) [] tp5 w (xrs_inclb_sound _ _ Fxix)) in HS3. rewrite FCX in HS3. exact HS3. }
  destruct (node_okb_sound _ _ FnCX) as (X1 & X2 & X3 & X4 & X5 & X6).
  apply (X_exit_call_ex AInv CST XGL ALA (KcG FDC evs) (KcG_ok _ _) rho0 P0 PTrue false nd_X 0 2 CXx (s_exR EBUF CXx) (R_xx CXx) X1 X3 Ffrx).
  + cbn. tauto.
  + intros tr md (_ & Hfd & _). rewrite Hfd. apply HFDC1.
  + intros w tr md (-> & Hfd & HX) Hw. apply (HS w md HX). rewrite Hw, Eevs, <- !app_assoc. reflexivity.
Qed.

Lemma tailF_free : ltac2:(tb__ "0|1|
S2dS5cA1M0S3eG0R1SafS46Q8A1S5cS60Sc2A1VmsgB;A4A3S3S2dS46Q40A1A1S70S45S6bS45S56S59VFDC;R4A2Vrho0;VP0;Vk;S147Vtb;Vtl;Vbd;A3A5VWx;R2R1A5VQ;A3Ftp;Frho;F_;Fevs;").
Proof.
  intros evs Eevs rho3 tp.
  destruct TFF as (Fn & Frun & Fx4 & Fsp & Cw3 & Cc3 & Cb3 & Fpub & FC & FnC & Ffr & Fcc & FT & Fsel & FS1o & FnbS1 & FU & FV & Fx4v & FW & FnW & FrunW
                   & Fxi & FCF & FnCF & FfrF & FccF & FcT & Fbb & Fs12 & Fs13 & Fpay & Fro & Fxr & Fnz & FTF & FnTF & FrunX
                   & FE1 & Fselx & Fmrg & Fspx & Fimg & Xw3 & Xc3 & Xb3 & Fx4x & Fxix & FCX & FnCX & Ffrx & Fccx).
  destruct (node_okb_sound _ _ FnW) as (W1 & W2 & W3 & W4 & W5 & W6).
  eapply JR_run; [unfold KU in Hk; lia | exact FrunW | exact W2 | exact W1 | exact W3 |].
  intros Lw rho4 [<-|[]] Hag4. cbn [la_state].

  eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF (KcG FDC evs) rho0 P0 [] [] BX0 PTrue (ndTk tb tl bd)) CFx rho4 tp)); [intros w HSP | intros w' Hw'; exact Hw' |].
  { apply (SPA_x_sub segs _ rho4 Fx (ax_X CFx) tp w (xrs_inclb_sound _ _ Fxi)) in HSP.
    assert (ECF : ax_setX Fx (ax_X CFx) = CFx) by (rewrite <- FCF; reflexivity). rewrite ECF in HSP.
    apply (SPA_JR_takeK (KcG FDC evs) rho0 P0 k KU [(tb, tl)] bd CFx rho4 tp w ltac:(unfold KU in *; lia) Hbdw) in HSP.
    apply (SPA_JR_dropBX _ rho0 P0 (k - KU) _ CFx rho4 tp w ltac:(unfold KU in *; lia)) in HSP.
    exact (SPA_JA_PA_weaken segs AInv CST XGL NF _ _ _ [] [] _ PA PTrue _ CFx _ tp w (fun _ _ => I) HSP). }
  destruct (node_okb_sound _ _ FnCF) as (G1 & G2 & G3 & G4 & G5 & G6).
  apply (X_free_call_ex AInv CST XGL ALA HCST HXGL HCSTdrv ACX (KcG FDC evs) (KcG_ok _ _) rho0 P0 PTrue (fun _ _ _ _ => I)
           tb tl [] (bd ++ [BIc 0 1 KU]) [] CFx sF RF TFx FfrF FccF FcT G1 (conj G3 Fbb) (conj Fs12 Fs13) Fpay G6 Fro Fxr Fnz FTF).
  intros rho5 tp5. apply (tailF_exit evs Eevs).
Qed.

Lemma tail_free : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;S147Vtb;Vtl;Vbd;A3A5VLx;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp.
  destruct TFF as (Fn & Frun & Fx4 & Fsp & Cw3 & Cc3 & Cb3 & Fpub & FC & FnC & Ffr & Fcc & FT & Fsel & FS1o & FnbS1 & FU & FV & Fx4v & FW & FnW & FrunW
                   & Fxi & FCF & FnCF & FfrF & FccF & FcT & Fbb & Fs12 & Fs13 & Fpay & Fro & Fxr & Fnz & FTF & FnTF & FrunX
                   & FE1 & Fselx & Fmrg & Fspx & Fimg & Xw3 & Xc3 & Xb3 & Fx4x & Fxix & FCX & FnCX & Ffrx & Fccx).
  destruct (node_okb_sound _ _ Fn) as (N1 & N2 & N3 & N4 & N5 & N6).

  eapply JR_run; [unfold KU in Hk; lia | exact Frun | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].

  eapply (etriple_conseq (P := SPA segs (JR KcC rho0 P0 k (ndT tb tl bd)) Cx rho1 tp)); [intros w HSP | intros w' Hw'; exact Hw' |].
  { pose proof HSP as [_ (Ai & kc & HJi)]. pose proof (SHR_now _ _ _ _ _ _ _ _ _ _ _ HP0 HJi) as [_ HZR].
    apply (SPA_x4set _ rho1 Ex (SLit TP) tp w Fx4) in HSP. change (x4set (SLit TP) Ex) with (TA1 Ex) in HSP.
    apply (SPA_split segs _ rho1 (TA1 Ex) 0 (SLit (-2528)) _ tp w Fsp) in HSP. rewrite <- (splitA_eq 0 (SLit (-2528)) (TA1 Ex) _ Fsp) in HSP. change (splitA 0 (SLit (-2528)) (TA1 Ex)) with (TA2 Ex) in HSP.
    assert (HS3 : SPA segs (JR KcC rho0 P0 k (ndT tb tl bd)) (TA3 Ex) rho1 tp w).
    { exact (carveR rho0 P0 k HP0SH KcC (ndT tb tl bd) (TA2 Ex) rho1 tp w N_fw (ss_next (ax_S (TA2 Ex))) HSP Cw3 (Pos.leb_refl _) Cb3 Cc3). }
    rewrite <- FC. apply (SPA_publish_lit2 _ rho1 (TA3 Ex) [(tb, tl)] tp w blkB blkL Fpub); [| |exact HS3].
    - exact (JR_tv_bandfree _ _ _ _ (ndT tb tl bd) _ _ _ _ (proj2 HS3)).
    - intros z Hz. apply HZR. apply Hblk. exact Hz. }
  destruct (node_okb_sound _ _ FnC) as (C1 & C2 & C3 & C4 & C5 & C6).

  set (Jfw := fun (_ : valuation) (t : list word) (tr : list event) (md : Model) => JR KcC rho0 P0 k (ndT tb tl bd) rho1 t tr md).
  assert (Jfw_stable : stableA segs NF Jfw).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jfw in HJ |- *. destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA (ss_next (ax_S Cx)) (ndT tb tl bd) Ai kc rho1 rho1 t tr md md' ltac:(apply Pos.leb_le; exact C1) C3 (agree_below_refl _ _) Hme HJ'). }
  assert (JfwK : forall r t tr md, Jfw r t tr md -> tr = T0 ++ [] /\ m_fds md = FDC /\ MDX md).
  { intros r t tr md HJ. exact (JR_Kc _ _ _ _ _ _ _ _ _ HJ). }
  apply (pure_callJ_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA KcC (KcG FDC ([] ++ DrvFw.EVS msg len (length (MSGB msg len))))
           Cx (Pre_fw msg len) sx Rx Posts_fw rho1 tp (ndT tb tl bd) Jfw (DrvFw.Kw Jfw msg len (length (MSGB msg len))) Q (KcG_ok _ _)).
  - intros rho2 tp2. apply (fwerr_sum_ex Jfw msg len Jfw_stable).
    + intros r t tr md HJ. destruct (JfwK _ _ _ _ HJ) as (_ & Hfd & _). rewrite Hfd. apply HFDC2.
    + exact Hfw.
  - exact Ffr.
  - exact Fcc.
  - exact C1.
  - exact C3.
  - exact C4.
  -   intros tr ms md Hsm HJ. exact HJ.
  -   intros rhoL tr' md' HK. exact (Kw_JR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK).
  -
    intros Lf rho2 HinL Hag2. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S Cx)) (import_postA sx (Pre_fw msg len) P_fw Cx Rx)) with (T_after (Pre_fw msg len) Cx sx Rx P_fw).
    rewrite FT. cbn [app]. set (evs := DrvFw.EVS msg len (length (MSGB msg len))).
    assert (Eevs : evs = map (WriteEv ch2) msgB).
    { unfold evs, DrvFw.EVS. rewrite firstn_all, Hmsg. reflexivity. }
    eapply (etriple_conseq (P := fun w => exists rho3, SPA segs (JR (KcG FDC evs) rho0 P0 k (ndT tb tl bd)) Wx rho3 tp w)); [intros w HSP | intros w' Hw'; exact Hw' |].
    { destruct w as [tr [ms md]].
      apply (SPA_axforms segs _ [AXSelect (fw_u1 (nobj Tx))] rho2 Tx (TS1 Tx) tp _ Fsel) in HSP.
      pose proof (uncarveR rho0 P0 k HP0SH (KcG FDC evs) (ndT tb tl bd) (TS1 Tx) rho2 tp tr ms md (ss_objs (ax_S Ux)) N_fw (KcG_ok _ _) FS1o N_fw_un eq_refl FnbS1 HSP) as HS2.
      rewrite FU in HS2. set (rho3 := rho_absorb rho2 (map lc_obj N_fw) (vms md tp ms)) in HS2. exists rho3.
      apply (SPA_axforms segs _ _ rho3 Ux Vx tp _ FV) in HS2.
      rewrite <- FW. exact (SPA_x4set _ rho3 Vx vTP tp _ Fx4v HS2). }
    apply etriple_ex. intros rho3. apply (tailF_free evs Eevs).
Qed.
End TailFree.

Lemma MSG_REF_eq : MSG_REF = msg_refused. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma Kwr_JR : ltac2:(tb__ "0|3|
S2dS2eS46Q40A1M0S5eA2A1S2dS5cA1M1S3S3OF_;S0S96S3S36S3S2dG0A1M2G1S5dS15cS3G2G1S5dS56S59R10RfA2ReRdRcRbRaR3R2R1A9Lmd;Ltr;Lt;L_;R5R4R3R2R1A6S56S59RdS35S5cRcS15bR6A1A3A2RbRaR9R8R7R4R3R2A9F_;Fmd';Ftr';Ft;FrhoL;Fn;Frho1;Fnd;Fk;FP0;Frho0;Fevs;Ffds;").
Proof.
  intros fds evs rho0 P0 k nd rho1 n rhoL t tr' md' (tr0 & HJ & ->).
  destruct HJ as (Ai & kc & Hav & (Htr & Hfd & HX) & REST). exists Ai, kc. split; [exact Hav|]. split; [|exact REST].
  split; [rewrite Htr, <- app_assoc; reflexivity|]. split; [exact Hfd | exact HX].
Qed.

Section TailRef.
Variables (len k : Z) (rho0 : valuation) (P0 : valuation -> Prop).
Hypothesis HP0R : ltac2:(tb__ "0|0|
S3VP0;R1A1S8cR2A1F_;Fr;").
Let HP0S : forall r, P0 r -> SH0 r := fun r H => proj1 (HP0R r H).
Hypothesis Hk : 0 <= k.
Hypothesis HSref : ltac2:(tb__ "0|0|
S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafS46Q8A1S5cS60Sc2A1S132A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;").

Lemma tail_ref : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5Sd8R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp.
  destruct ref_facts as (On & Ox4 & Osp & Ocv & Opub & OC & Ofb & OnC & OT & Osel & OS1o & OnbS1 & OU & OV & OnV & OLV & Ob1 & Oimg & Ocv2 & Ox4b & Oxi & OCX & OnCX & Ofr & Occ).
  destruct (node_okb_sound _ _ On) as (N1 & N2 & N3 & N4 & N5 & N6).

  eapply JR_run; [exact Hk | exact run_ref1 | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].

  unfold carve_chk in Ocv. apply andb_prop in Ocv as [Ocv Cb3]. apply andb_prop in Ocv as [Cw3 Cc3]. apply sv_eqb_sound in Cb3.
  eapply (etriple_conseq (P := SPA segs (JR (KcR len) rho0 P0 k nd_R) C_ref rho1 tp)); [intros w HSP | intros w' Hw'; exact Hw' |].
  { pose proof HSP as [_ (Ai & kc & HJi)]. pose proof (SHR_now _ _ _ _ _ _ _ _ _ _ _ HP0R HJi) as [_ HZR].
    apply (SPA_x4set _ rho1 E_ref (SLit TP) tp w Ox4) in HSP. change (x4set (SLit TP) E_ref) with A1_ref in HSP.
    apply (SPA_split segs _ rho1 A1_ref 0 (SLit (-2688)) _ tp w Osp) in HSP. rewrite <- (splitA_eq 0 (SLit (-2688)) A1_ref _ Osp) in HSP. change (splitA 0 (SLit (-2688)) A1_ref) with A2_ref in HSP.
    assert (HS3 : SPA segs (JR (KcR len) rho0 P0 k nd_R) A3_ref rho1 tp w).
    { exact (carveR rho0 P0 k HP0S (KcR len) nd_R A2_ref rho1 tp w N_fp (ss_next (ax_S A2_ref)) HSP Cw3 (Pos.leb_refl _) Cb3 Cc3). }
    clear HSP. apply (SPA_publish_lit2 _ rho1 A3_ref [(vB, vCap)] tp w 0x1a7c0 0x80 Opub (JR_tv_bandfree _ _ _ _ nd_R _ _ _ _ (proj2 HS3))) in HS3; [| intros z Hz; apply HZR; right; right; exact Hz].
    change (ax_setX A3_ref _) with A4_ref in HS3.
    rewrite <- OC. unfold ax_add_facts. change (ax_setS A4_ref (add_facts [ms16_at sp0 2456] (ax_S A4_ref))) with (ax_with_facts A4_ref ([ms16_at sp0 2456] ++ ss_facts (ax_S A4_ref))).
    apply (SPA_refacts_JA segs); [exact HS3 | exact Ofb |].
    intros tr md _ HF'. apply Forall_app. split; [|exact HF']. constructor; [apply ms16_at_holds | constructor]. }
  destruct (node_okb_sound _ _ OnC) as (C1 & C2 & C3 & C4 & C5 & C6).

  set (Jfp := fun (_ : valuation) (t : list word) (tr : list event) (md : Model) => JR (KcR len) rho0 P0 k nd_R rho1 t tr md).
  assert (Jfp_stable : stableA segs NF Jfp).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jfp in HJ |- *. destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA (ss_next (ax_S C_ref)) nd_R Ai kc rho1 rho1 t tr md md' ltac:(apply Pos.leb_le; exact C1) C3 (agree_below_refl _ _) Hme HJ'). }
  assert (JfpK : forall r t tr md, Jfp r t tr md -> tr = T0 ++ [] /\ m_fds md = FDS len /\ MDX md).
  { intros r t tr md HJ. exact (JR_Kc _ _ _ _ _ _ _ _ _ HJ). }
  apply (pure_callJ_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA (KcR len) (KcG (FDS len) ([] ++ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp.EVSr 38))
           C_ref Pre_ref s_ref R_ref Posts_ref rho1 tp nd_R Jfp (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp.Kwr Jfp 38) Q (KcG_ok _ _)).
  - intros rho2 tp2. apply (ref_sum_ex Jfp Jfp_stable).
    + intros r t tr md HJ. destruct (JfpK _ _ _ _ HJ) as (_ & Hfd & _). rewrite Hfd. apply HFDS2.
  - exact fr_ref.
  - exact cc_ref.
  - exact C1.
  - exact C3.
  - exact C4.
  -   intros tr ms md Hsm HJ. exact HJ.
  -   intros rhoL tr' md' HK. exact (Kwr_JR _ _ _ _ _ _ _ _ _ _ _ _ HK).
  -
    intros Lf rho2 HinL Hag2. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S C_ref)) (import_postA s_ref Pre_ref P_ref C_ref R_ref)) with (T_after Pre_ref C_ref s_ref R_ref P_ref).
    rewrite OT. cbn [app]. set (evs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp.EVSr 38).
    assert (Eevs : evs = map (WriteEv ch2) msg_refused).
    { unfold evs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp.EVSr. rewrite MSG_REF_eq. reflexivity. }
    eapply (etriple_conseq (P := fun w => exists rho3, SPA segs (JR (KcG (FDS len) evs) rho0 P0 k nd_R) V_ref rho3 tp w)); [intros w HSP | intros w' Hw'; exact Hw' |].
    { destruct w as [tr [ms md]].
      apply (SPA_axforms segs _ [AXSelect (fp_u1 (nobj T_ref))] rho2 T_ref S1_ref tp _ Osel) in HSP.
      pose proof (uncarveR rho0 P0 k HP0S (KcG (FDS len) evs) nd_R S1_ref rho2 tp tr ms md (ss_objs (ax_S U_ref)) N_fp (KcG_ok _ _) OS1o N_fp_un eq_refl OnbS1 HSP) as HS2.
      rewrite OU in HS2. set (rho3 := rho_absorb rho2 (map lc_obj N_fp) (vms md tp ms)) in HS2. exists rho3.
      exact (SPA_axforms segs _ _ rho3 U_ref V_ref tp _ OV HS2). }
    apply etriple_ex. intros rho3.
    destruct (node_okb_sound _ _ OnV) as (V1 & V2 & V3 & V4 & V5 & V6).
    pose proof run_xref as RX. rewrite OLV in RX.
    eapply JR_run; [exact Hk | exact RX | exact V2 | exact V1 | exact V3 |].
    intros Lx rho4 [<-|[]] Hag4. cbn [la_state].

    unfold carve_chk in Ocv2. apply andb_prop in Ocv2 as [Ocv2 Xb3]. apply andb_prop in Ocv2 as [Xw3 Xc3]. apply sv_eqb_sound in Xb3.
    eapply (etriple_conseq (P := SPA segs (JR (KcG (FDS len) evs) rho0 P0 k nd_R) CX_ref rho4 tp)); [intros w HSP | intros w' Hw'; exact Hw' |].
    { apply (SPA_split segs _ rho4 X_ref 0 (SLit (-1152)) _ tp w Ob1) in HSP. rewrite <- (splitA_eq 0 (SLit (-1152)) X_ref _ Ob1) in HSP.
      apply (SPA_x_sub segs _ rho4 _ [] tp w ltac:(intros rr Hrr; destruct Hrr)) in HSP. change (ax_setX (splitA 0 (SLit (-1152)) X_ref) []) with B1_ref in HSP.
      apply (SPA_img_cell segs _ rho4 B1_ref _ _ _ _ tp w Oimg) in HSP. change (ax_setS B1_ref _) with B2_ref in HSP.
      assert (HS3 : SPA segs (JR (KcG (FDS len) evs) rho0 P0 k nd_R) B3_ref rho4 tp w).
      { exact (carveR rho0 P0 k HP0S (KcG (FDS len) evs) nd_R B2_ref rho4 tp w N_exR (ss_next (ax_S B2_ref)) HSP Xw3 (Pos.leb_refl _) Xb3 Xc3). }
      clear HSP.
      apply (SPA_x4set _ rho4 B3_ref (SLit TP) tp w Ox4b) in HS3. change (x4set (SLit TP) B3_ref) with B4_ref in HS3.
      apply (SPA_x_sub segs _ rho4 B4_ref [] tp w (xrs_inclb_sound _ _ Oxi)) in HS3. rewrite OCX in HS3. exact HS3. }
    eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF (KcG (FDS len) evs) rho0 P0 [] [] BX0 PA nd_R) CX_ref rho4 tp));
      [intros w HSP; exact (SPA_JR_dropBX _ rho0 P0 k nd_R CX_ref rho4 tp w Hk HSP) | intros w' Hw'; exact Hw' |].
    destruct (node_okb_sound _ _ OnCX) as (X1 & X2 & X3 & X4 & X5 & X6).
    apply (X_exit_call_ex AInv CST XGL ALA (KcG (FDS len) evs) (KcG_ok _ _) rho0 P0 PA false nd_R 0 2 CX_ref (s_exR 0 CX_ref) R_xref X1 X3 Ofr).
    + cbn. tauto.
    + intros tr md (_ & Hfd & _). rewrite Hfd. apply HFDS1.
    + intros w tr md (-> & Hfd & HX) Hw. apply (HSref w md HX). rewrite Hw, Eevs, <- !app_assoc. reflexivity.
Qed.
End TailRef.

Lemma blk_sh : ltac2:(tb__ "0|1|
S0S3fS4aS112Z21440M0A1R1A2S4cR1S112S4bG0Z40A2A1A2A2S90R2A1F_;Fz;").
Proof. intros z Hz. left. unfold Sh, SHADOW_OFF in *. lia. Qed.
Lemma blk_ov : ltac2:(tb__ "0|1|
S0S3fS4aS112Z16080M0A1R1A2S4cR1S112S4bG0Z40A2A1A2A2S90R2A1F_;Fz;").
Proof. intros z Hz. right. left. unfold Sh, SHADOW_OFF in *. lia. Qed.
Lemma fw_in_sh : ltac2:(tb__ "0|0|
ScbS2eS0S0A2S38S0S0Z21441Z1fA4S139A3"). Proof. cbn. tauto. Qed.
Lemma fw_in_ov : ltac2:(tb__ "0|0|
ScbS2eS0S0A2S38S0S0Z1609eZ1fA4S139A3"). Proof. cbn. tauto. Qed.

Lemma U_lit64 : ltac2:(tb__ "0|0|
S3S0S3fS4aZ0R1A2S4cR1S4eZ2Z40A2A2A2S3eS0S47Q40S7R3S8R2A1A2A2R2A3F_;Fz;Frho;").
Proof. intros rho z Hz. rewrite U_lit. unfold M64v. apply Z.mod_small. exact Hz. Qed.

Lemma len_le5_of_fact : ltac2:(tb__ "0|2|
S3S2dS6A1S0Sb0S6ScR3A1R2A3S3eS31ScaS6SdS16S13dS8Z5M0A1S10P2aM1A1A3A1R3A3S30A3S3eS0S47Q40S4R5G1A2A2R3A3S4aR4G0A2F_;F_;F_;Flen;Ffacts;Frho;").
Proof.
  intros rho facts len HF H5 Hlen.
  pose proof (holds_fact rho _ _ HF H5) as X. cbn [holds branch_taken] in X. unfold bv_ltu in X.
  change (eval rho (SVar 42%positive)) with (rw rho 42%positive) in X. rewrite Hlen in X. rewrite (U_lit64 rho 5 ltac:(lia)) in X.
  destruct (Z.ltb_spec 5 len); [cbn in X; discriminate X | lia].
Qed.
Lemma len_ge6_of_fact : ltac2:(tb__ "0|1|
S3S2dS6A1S0Sb0S6ScR3A1R2A3S3eS31ScaS6SdS20S16S13dS8Z5A1S10P2aM0A1A3A1A1R3A3S30A3S3eS0S47Q40S4R5G0A2A2R3A3S4aZ6R4A2F_;F_;F_;Flen;Ffacts;Frho;").
Proof.
  intros rho facts len HF H5 Hlen.
  pose proof (holds_fact rho _ _ HF H5) as X. cbn [holds branch_taken] in X. unfold bv_ltu in X.
  change (eval rho (SVar 42%positive)) with (rw rho 42%positive) in X. rewrite Hlen in X. rewrite (U_lit64 rho 5 ltac:(lia)) in X.
  destruct (Z.ltb_spec 5 len); [lia | exfalso; apply X; reflexivity].
Qed.
Lemma len_lt_clen_of_fact : ltac2:(tb__ "0|3|
S3S2dS6A1S0Sb0S6ScR3A1R2A3S3eS31ScaS6SdS16S143S10P2aM0A1S1eS140Sf5S8Z6M1A1A3A3A1R3A3S30A3S3eS0S47Q40M2S4R5G0A2A2R3A3S3eS0S51S47G2S4R6P2dA2A2S4eZ2Z20A2A2S100VF;A1A3S4cR5S4bG1S103VF;A1A2A2F_;F_;F_;F_;Flen;Ffacts;Frho;").
Proof.
  intros rho facts len HF Hlt Hlen Hh. pose proof (clen_of_range F) as HCR.
  pose proof (holds_fact rho _ _ HF Hlt) as X. cbn [holds branch_taken] in X. unfold bv_ltu in X.
  change (eval rho (SVar 42%positive)) with (rw rho 42%positive) in X. rewrite Hlen in X.
  assert (E2 : bv_unsigned (eval rho (SAlu ALU_ADD clen_x (SLit 6))) = clen_of F + 6).
  { rewrite CursorGlue.U_add, U_lit, (U_clen_x F rho Hh). unfold M64v. rewrite (Z.mod_small 6) by lia. apply Z.mod_small. lia. }
  rewrite E2 in X. destruct (Z.ltb_spec len (clen_of F + 6)); [lia | cbn in X; discriminate].
Qed.

Section TailInst.
Hypothesis HSref : ltac2:(tb__ "0|1|
S4aS131S4dS32S46Q8A1M0VF;A2A1A2S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafG0S5cS60Sc2A1S132A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;F_;").
Hypothesis HSsh : ltac2:(tb__ "0|1|
S4cS4dS32S46Q8A1M0VF;A2A1Z6A2S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafG0S5cS60Sc2A1S134A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;F_;").
Hypothesis HSov : ltac2:(tb__ "0|3|
S3fS4aZ6M0S4dS32S46Q8A1M1VF;A2A1M2A2S4cG2S4bG0S103VF;A1A2A2A2S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafG1S5cS60Sc2A1S133A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;F_;").

Theorem HTsh_ok : ltac2:(tb__ "0|0|
S36S0S0S0S3Sc5R5UaA2S3fS4aZ4R5A2S4cR5S8bR6A1A2A2S3eS0R6S4dS32S46Q8A1VF;A2A1A3S3fS4aZ1R6A2S4aR6Z10000A2A2S4aSb3R6A2S3S2dS46Q40A1A1S70S45S6bS45S56S58R8S8eRcRbRaVF;A4R9S75A5SddR2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;F_;Frho0;Fk;Fwant;Flen;Fg;").
Proof.
  intros g len want k rho0 Hg Hlen HlenF Hw Hk rho tp.
  apply etriple_factsA. intros HF.
  apply (triple_pre _ _ (Z.of_nat (length F) < 6)).
  { intros w HS. destruct (SPA_JR_facts _ _ _ _ _ _ _ _ _ HS) as ([(Q24 & Q32 & _) _] & Hav & _).
    rewrite <- (U_agree rho0 rho 42%positive Hav ltac:(cbv; reflexivity)) in Q32. unfold U in Q32.
    pose proof (len_le5_of_fact rho _ len HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Q32). lia. }
  intros HF6.
  exact (tail_free vB vCap bd_R 0x21441 31 0x21440 0x40 Lsh1 E_sh1 C_sh1 T_sh1 U_sh1 V_sh1 W_sh1 F_sh1 CF_sh1 TF_sh1 X_sh1 CX_sh1 s_sh1 sF_sh1 R_sh1 RF_sh1
           msg_short fw_in_sh MSGB_short blk_sh (P0RD1 g len want F) k rho0 (P0RD1_SHR g len want) Hk eq_refl sh1_facts (HSsh HF6) rho tp).
Qed.

Theorem HTov_ok : ltac2:(tb__ "0|0|
S36S0S0S0S3Sc5R5UaA2S3fS4aZ4R5A2S4cR5S8bR6A1A2A2S3eS0R6S4dS32S46Q8A1VF;A2A1A3S3fS4aZ1R6A2S4aR6Z10000A2A2S4aSb3R6A2S3S2dS46Q40A1A1S70S45S6bS45S56S58R8S8eRcRbRaVF;A4R9S75A5SdcR2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;F_;Frho0;Fk;Fwant;Flen;Fg;").
Proof.
  intros g len want k rho0 Hg Hlen HlenF Hw Hk rho tp.
  apply etriple_factsA. intros HF.
  apply (triple_pre _ _ (6 <= Z.of_nat (length F) < 6 + clen_of F)).
  { intros w HS. destruct (SPA_JR_facts _ _ _ _ _ _ _ _ _ HS) as ([(Q24 & Q32 & Q31 & Q35 & _) _] & Hav & _).
    rewrite <- (U_agree rho0 rho 42%positive Hav ltac:(cbv; reflexivity)) in Q32. unfold U in Q32.
    rewrite <- (U_agree rho0 rho 45%positive Hav ltac:(cbv; reflexivity)) in Q35. unfold U in Q35.
    pose proof (len_ge6_of_fact rho _ len HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Q32).
    pose proof (len_lt_clen_of_fact rho _ len HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Q32 Q35). lia. }
  intros HF6.
  exact (tail_free vB vCap bd_R 0x1609e 31 0x16080 0x40 Lov1 E_ov1 C_ov1 T_ov1 U_ov1 V_ov1 W_ov1 F_ov1 CF_ov1 TF_ov1 X_ov1 CX_ov1 s_ov1 sF_ov1 R_ov1 RF_ov1
           msg_overrun fw_in_ov MSGB_overrun blk_ov (P0RD1 g len want F) k rho0 (P0RD1_SHR g len want) Hk eq_refl ov1_facts (HSov HF6) rho tp).
Qed.

Theorem HTref_ok : ltac2:(tb__ "0|0|
S36S0S0S0S0S3Sc5R6UaA2S4aZ4R6A2S3fS4aZ1R5A2S4aR5R6A2A2S4aR7Z10000A2S3eS0S4bR9R7A2S8bRaA1A3S4aS4eZ2Z1aA2S8bRbA1A2S4aS4bRbR9A2S4dS32S46Q8A1VF;A2A1A2S4aSb3R9A2S3S2dS46Q40A1A1S70S45S6bS45S56S57S4bRfRdA2A1RbS8eR10RfReVF;A4RcS75A5Sd8R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;F_;F_;F_;F_;Frho0;Fk;Fres;Fwant;Flen;Fg;").
Proof.
  intros g len want res k rho0 Hg Hlen Hres Hw Hlc H26 HlenF Hk rho tp.
  apply (tail_ref (len + res) k rho0 (P0RD1 g len want F) (P0RD1_SHR g len want) ltac:(unfold KU in Hk; lia)). apply HSref. unfold MAX_INPUT. lia.
Qed.

End TailInst.

Lemma bl2z_nonneg : ltac2:(tb__ "0|0|
S2dS46Q8A1A1S4aZ0S135R1A1A2Fl;").
Proof.
  induction l as [|b l IH]; cbn [bytes_le_to_Z]; [lia|].
  apply (proj2 (Z.lor_nonneg _ _)). split; [pose proof (bv_unsigned_in_range 8 b); lia | apply (proj2 (Z.shiftl_nonneg _ _)); exact IH].
Qed.
Lemma bl2z_cons : ltac2:(tb__ "0|2|
S46Q8M0A1M1S2dG1A1S3eS0S135S37G1R2R1A3A1S4bS47G0R2A2S4fZ100S135R1A1A2A2A3Fl;Fb;").
Proof.
  intros b l. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  apply lor_shiftl8; [lia | apply bl2z_nonneg].
Qed.

Lemma hdr_val_word : ltac2:(tb__ "0|2|
S36Sc5U4M0S32S46Q8A1M1VF;A2A2Sc5G0R2A2S3eS0S47Q40S167Sb1G1R3VF;A3A1A2S100VF;A1A3F_;F_;Fn;").
Proof.
  intros n HF Hn. unfold hdr_val. rewrite firstn_firstn. replace (Nat.min 4 n) with 4%nat by lia.
  destruct F as [|b0 [|b1 [|b2 [|b3 rest]]]]; try (cbn in HF; lia).
  change (firstn 4 (b0 :: b1 :: b2 :: b3 :: rest)) with [b0; b1; b2; b3].
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. change (bv_modulus 8) with 256 in *.
  rewrite !bl2z_cons. change (bytes_le_to_Z []) with 0. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia).
  unfold hdr_word. cbn [nth]. lia.
Qed.

Lemma resZ_of_fact : ltac2:(tb__ "0|1|
S3S2dS6A1S1Sb0S6ScR3A1R2A3S3eS31ScaS6SdS20S16S13eS10R2A1S8Z0M0A1A3A1A1R3A3S30A3S3eS0S47Q40S4R5R3A2A2G0A3F_;F_;Fv;Ffacts;Frho;").
Proof.
  intros rho facts v HF H. pose proof (holds_fact rho _ _ HF H) as X. cbn [holds eval branch_taken] in X. unfold bv_eqb in X.
  rewrite lit_unsigned in X. change (0 mod 2 ^ 64) with 0 in X.
  destruct (Z.eqb_spec (bv_unsigned (rw rho v)) 0) as [E0|NE]; [exact E0|]. exfalso. apply X. reflexivity.
Qed.
Lemma resNZ_of_fact : ltac2:(tb__ "0|1|
S3S2dS6A1S1Sb0S6ScR3A1R2A3S3eS31ScaS6SdS16S13eS10R2A1S8Z0M0A1A3A1R3A3S30A3S44S3eS0S47Q40S4R5R3A2A2G0A3A1F_;F_;Fv;Ffacts;Frho;").
Proof.
  intros rho facts v HF H. pose proof (holds_fact rho _ _ HF H) as X. cbn [holds eval branch_taken] in X. unfold bv_eqb in X.
  rewrite lit_unsigned in X. change (0 mod 2 ^ 64) with 0 in X.
  destruct (Z.eqb_spec (bv_unsigned (rw rho v)) 0) as [E0|NE]; [cbn in X; discriminate | exact NE].
Qed.

Definition lit_cells (cs : list cell) : Prop := ltac2:(tb__ "0|3|
Sb0S9S9S5OLx;S18R1A1S0S3fS4aZ0R1A2S4aR1Z10000A2A2Lz;S1S40Li;S145S5S5S40Lb;La;M0Lop;M1G1S146G0Lop;M2G2S31S2S5S40La;Lw;Lsgn;S1S5S0S40Lk;Li;Ll;X5x8Lc;Vcs;A3").
Lemma lit_cells_nil : lit_cells []. Proof. constructor. Qed.
Lemma lit_cells_hcZ : lit_cells hcZ. Proof. unfold lit_cells, hcZ. constructor; [cbn; lia | constructor]. Qed.
Lemma rds_cells_up : ltac2:(tb__ "0|0|
S3S2dS9A1S5aR1A1SccS9S9S9S9S3fS3eS0S1bR1A1S1bR2A1A3S3fS3eS5S1aR1A1S1aR2A1A3S3eS0S1cR5S18R1A1A2S50S1cR5S18R2A1A2S55Sd4A1A2A3A2A2Lc';Lc;R2SdbR2A1A5F_;Fcs;Frho;").
Proof.
  intros rho cs H. induction H as [|c cs Hc _ IH]; [constructor|]. cbn [rds_cellsL map]. constructor; [|exact IH].
  destruct c as [off w v]. cbn [c_off] in Hc |- *. destruct off as [z| | | | | | |]; try contradiction.
  cbn [c_width SymState.c_val c_off]. split; [reflexivity|]. split; [reflexivity|].
  rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). lia.
Qed.
Lemma rds_cells_down : ltac2:(tb__ "0|0|
S3S2dS9A1S5aR1A1SccS9S9S9S9S3fS3eS0S1bR1A1S1bR2A1A3S3fS3eS5S1aR1A1S1aR2A1A3S3eS0S1cR5S18R1A1A2S50S1cR5S18R2A1A2Sd4A2A3A2A2Lc';Lc;SdbR2A1R2A5F_;Fcs;Frho;").
Proof.
  intros rho cs H. induction H as [|c cs Hc _ IH]; [constructor|]. cbn [rds_cellsL map]. constructor; [|exact IH].
  destruct c as [off w v]. cbn [c_off] in Hc |- *. destruct off as [z| | | | | | |]; try contradiction.
  cbn [c_width SymState.c_val c_off]. split; [reflexivity|]. split; [reflexivity|].
  rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). lia.
Qed.

Lemma rdsW_to_ZL : ltac2:(tb__ "0|0|
S2dS9A1S3S118S5aR3A1S14S45R3R2S78R4A1A4S14S45R4R3S79R5A1A4F_;F_;Fms;Frho;Fcs;").
Proof.
  intros cs rho ms Hcs. apply (obj_holds_shift rho ms (O_rdsW cs) (O_rdsZL cs) (- RS)); [reflexivity | reflexivity | | | | |].
  - unfold O_rdsW, O_rdsZL. cbn [ob_base]. rewrite !U_lit. cbn. reflexivity.
  - unfold O_rdsW, O_rdsZL, obj_lo_of. cbn [ob_lo]. rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). lia.
  - unfold O_rdsW, O_rdsZL, obj_hi_of. cbn [ob_hi]. rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). lia.
  - unfold O_rdsZL, obj_hi_of, obj_lo_of. cbn [ob_hi ob_lo]. rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). unfold RS, RD_STAGE. lia.
  - exact (rds_cells_up rho cs Hcs).
Qed.
Lemma rdsW_ZL_range : ltac2:(tb__ "0|0|
S2dS9A1S3S3eS2eS0S0A2SeR1S79R2A1A2SeR1S78R2A1A2A3Frho;Fcs;").
Proof.
  intros cs rho. unfold obj_range, obj_lo_of, obj_hi_of, O_rdsZL, O_rdsW. cbn [ob_base ob_lo ob_hi].
  rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). rewrite !U_lit. cbn. reflexivity.
Qed.

Lemma rdsP_to_L : ltac2:(tb__ "0|0|
S5S2dS9A1S3S118S5aR3A1S4aS47Q40S7R3R5A2A2Z10000A2S14S45R4R3S1fS8Sd4A1S8Z0A1R6R5S1dA5A4S14S45R5R4Sd9R7SdbR6A1A2A4F_;F_;F_;Fms;Frho;Fcs;Fr;").
Proof.
  intros r cs rho ms Hcs Hr. pose proof (urange (eval rho r)).
  assert (E2 : soff rho (add (SLit RS) r) = RS + bv_unsigned (eval rho r)).
  { unfold soff, add. rewrite signed_small by (rewrite U_add, U_lit, <- !M64v_eq, (Z.mod_small RS), Z.mod_small; unfold RS, RD_STAGE; lia).
    rewrite U_add, U_lit, <- !M64v_eq, (Z.mod_small RS), Z.mod_small; unfold RS, RD_STAGE; lia. }
  assert (E4 : soff rho r = bv_unsigned (eval rho r)) by (unfold soff; rewrite signed_small by lia; reflexivity).
  apply (obj_holds_shift rho ms (mkObj (SLit RS) (SLit 0) r cs DUnknown) (O_rdsL r (rds_cellsL cs)) (- RS)); [reflexivity | reflexivity | | | | |].
  - unfold O_rdsL. cbn [ob_base]. rewrite !U_lit. cbn. reflexivity.
  - unfold O_rdsL, obj_lo_of. cbn [ob_lo]. rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). lia.
  - unfold O_rdsL, obj_hi_of. cbn [ob_hi]. rewrite E2, E4. lia.
  - unfold O_rdsL, obj_hi_of, obj_lo_of. cbn [ob_hi ob_lo]. rewrite E2, soff_lit_small by (unfold RS, RD_STAGE; lia). lia.
  - exact (rds_cells_up rho cs Hcs).
Qed.

Lemma rdsL_to_C : ltac2:(tb__ "0|0|
S5S2dS9A1S3S118S5aR3A1S4aS47Q40S7R3R5A2A2Z10000A2S14S45R4R3Sd9R6SdbR5A1A2A4S14S45R5R4Se7R7R6A2A4F_;F_;F_;Fms;Frho;Fcs;Fr;").
Proof.
  intros r cs rho ms Hcs Hr. pose proof (urange (eval rho r)).
  assert (E2 : soff rho (add (SLit RS) r) = RS + bv_unsigned (eval rho r)).
  { unfold soff, add. rewrite signed_small by (rewrite U_add, U_lit, <- !M64v_eq, (Z.mod_small RS), Z.mod_small; unfold RS, RD_STAGE; lia).
    rewrite U_add, U_lit, <- !M64v_eq, (Z.mod_small RS), Z.mod_small; unfold RS, RD_STAGE; lia. }
  assert (E4 : soff rho r = bv_unsigned (eval rho r)) by (unfold soff; rewrite signed_small by lia; reflexivity).
  apply (obj_holds_shift rho ms (O_rdsL r (rds_cellsL cs)) (O_rdsC r cs) RS); [reflexivity | reflexivity | | | | |].
  - unfold O_rdsL, O_rdsC. cbn [ob_base]. rewrite U_rdsb, U_lit. cbn. reflexivity.
  - unfold O_rdsL, O_rdsC, obj_lo_of. cbn [ob_lo]. rewrite !soff_lit_small by (unfold RS, RD_STAGE; lia). lia.
  - unfold O_rdsL, O_rdsC, obj_hi_of. cbn [ob_hi]. rewrite E2, E4. lia.
  - unfold O_rdsC, obj_hi_of, obj_lo_of. cbn [ob_hi ob_lo]. rewrite E4, soff_lit_small by lia. lia.
  - exact (rds_cells_down rho cs Hcs).
Qed.

Lemma rdsZ_range : ltac2:(tb__ "0|3|
S3S3fS3eS2eS0S0A2SeR1Se7S8S125A1S2fS9A1A2M0A2SeR1S7bA2A3S3fS4aS15R1G0A2M1S13R1G0A2M2A2S4cS50G2G1A2S4eZ2Z3fA2A2A2A2Frho;").
Proof.
  intros rho. unfold obj_range, obj_lo_of, obj_hi_of, O_rdsC, O_rdsZ. cbn [ob_base ob_lo ob_hi].
  rewrite U_rdsb, !U_lit, !soff_lit_small by (unfold RS, RD_STAGE, CAP0; lia). unfold RS, RD_STAGE, CAP0. cbn. repeat split; reflexivity || lia.
Qed.

Lemma qz_cleanup : ltac2:(tb__ "0|1|
Sa8S3S3OF_;S0S2dS9A1S80S80S80S80S3S2dS46Q40A1M0A1S71Sa9RcA1S5aR9A1S7fRaR9R8R7R6A5S3ReR1A1Sf7R2A1F_;Fr;S6bS45S56R10RfReRdS76A5RbR7R6R5A6S41S3S3S3fS1S3eG0S4R2R1A2S4RaR1A2A3Fv;S6bS45S56R12R11R10RfS76A5RaR1R8R7A6A2Lrho';A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;FQd;FQb;FQa;FLf;Fcs;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k cs Lf Qa Qb Qd rho tp w HKc Hcs HQ HP0 HS.
  destruct HQ as (Xa & Hn & Hset & Hsame & HXb & Hbb & Hobjs & Hnb & HX & HQd & _).
  destruct w as [tr [ms md]].
  apply (SPA_axforms segs _ XF_qz rho Lf Qa tp _ Xa) in HS.
  apply (SPA_reobj_same_range _ rho Qa 38 _ (O_rdsZL cs) tp _ Hn ltac:(rewrite Hset; exact Hsame) (rdsW_ZL_range cs rho) (fun ms => rdsW_to_ZL cs rho ms Hcs)) in HS.
  rewrite Hset in HS.
  assert (EQb : ax_setS Qa (ax_S Qb) = Qb) by (destruct Qa, Qb; cbn in HXb, Hbb |- *; subst; reflexivity). rewrite EQb in HS.
  pose proof (uncarveR rho0 P0 k HP0 Kc nd_Z Qb rho tp tr ms md (objs37 Qb) N_rd HKc ltac:(rewrite N_rd_eq; exact Hobjs) N_rd_un eq_refl Hnb HS) as HS2.
  set (rho' := rho_absorb rho (map lc_obj N_rd) (vms md tp ms)) in HS2. exists rho'. split; [intros v; reflexivity|].
  rewrite <- HQd. apply SPA_x_sub; [exact (xrs_inclb_sound _ _ HX) | exact HS2].
Qed.

Lemma bkz_cleanup : ltac2:(tb__ "0|2|
Sa8S3S3OF_;S0S5S2dS9A1S80S80S80S80S80S3S2dS46Q40M0A1M1A1S71Sa9ReA1S5aRaA1S7dRcRbRaR9R8R7R6A7S4aS47G0S7R6RdA2A2Z10000A2S3R11R1A1Sf7R2A1F_;Fr;S6bS45S56R13R12R11R10S76A5RdR8R7R6A6S41S3S3S3fS1S3eG1S4R2R1A2S4RbR1A2A3Fv;S6bS45S56R15R14R13R12S76A5RbR1R9R8A6A2Lrho';A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FB;FBc;FBb;FBa;FLf;Fcs;Fr;Fk;FP0;Frho0;FKc;").
Proof.
  intros Kc rho0 P0 k r cs Lf Ba Bb Bc B rho tp w HKc Hcs HB Hr HP0 HS.
  destruct HB as (Xa & Hn & Hset & Hsame & HXb & Hbb & Xc & Hobjs & Hnb & HX & HBe & _).
  destruct w as [tr [ms md]].
  apply (SPA_axforms segs _ XF_bkza rho Lf Ba tp _ Xa) in HS.
  assert (RR : obj_range rho (O_rdsL r (rds_cellsL cs)) = obj_range rho (mkObj (SLit RS) (SLit 0) r cs DUnknown)).
  { exact (proj1 (rds_ranges rho (SLit RS) r cs (U_RS rho) Hr)). }
  apply (SPA_reobj_same_range _ rho Ba 39 _ (O_rdsL r (rds_cellsL cs)) tp _ Hn ltac:(rewrite Hset; exact Hsame) RR (fun ms => rdsP_to_L r cs rho ms Hcs Hr)) in HS.
  rewrite Hset in HS.
  assert (EQb : ax_setS Ba (ax_S Bb) = Bb) by (destruct Ba, Bb; cbn in HXb, Hbb |- *; subst; reflexivity). rewrite EQb in HS.
  apply (SPA_axforms segs _ XF_bkzb rho Bb Bc tp _ Xc) in HS.
  pose proof (uncarveR rho0 P0 k HP0 Kc nd_Z Bc rho tp tr ms md (objs37 Bc) N_mc HKc Hobjs N_mc_un eq_refl Hnb HS) as HS2.
  set (rho' := rho_absorb rho (map lc_obj N_mc) (vms md tp ms)) in HS2. exists rho'. split; [intros v; reflexivity|].
  rewrite <- HBe. apply SPA_x_sub; [exact (xrs_inclb_sound _ _ HX) | exact HS2].
Qed.

Section FirstRead.
Variables (k : Z) (rho0 : valuation) (P0 : valuation -> Prop).
Hypothesis HP0 : ltac2:(tb__ "0|0|
S3VP0;R1A1S3fS3eS0S8fR2P18A2SffA3S8cR2A1A2F_;Fr;").
Hypothesis Hk : 0 <= k.
Definition res0 : Z := Z.min 65536 (Z.of_nat (length F)).
Definition BS0 : list byte := firstn (Z.to_nat 65536) F.
Lemma BS0_len : ltac2:(tb__ "0|0|
S3eS0S4dS32S46Q8A1Sd1A2A1ScfA3").
Proof. unfold BS0, res0. rewrite length_firstn. lia. Qed.
Let HP0SH : forall r, P0 r -> SH0 r := fun r H => proj1 (proj2 (HP0 r H)).
Let HP0SHR : forall r, P0 r -> SHR r := fun r H => proj2 (HP0 r H).

Hypothesis HcopyK : ltac2:(tb__ "0|2|
S3fS4aZ1S4dS32S46Q8A1VF;A2A1M0A2S4aG0Z3A2A2S3S2dS46Q40M1A1A1S3eS0S47G1S4R2P64A2A2ScfA3S70S45S6bS45S56S57ScfA1Vrho0;VP0;Vk;S76A5SeaR3R2A5VQ;A3F_;Ftp';Frho';F_;").
Hypothesis HcopyH : ltac2:(tb__ "0|1|
S4aZ4S4dS32S46Q8A1VF;A2A1A2S3S2dS46Q40M0A1A1S3eS0S47G0S4R2P65A2A2ScfA3S3eS0S47G0S4R3P64A2A2S100VF;A1A3S70S45S6bS45S56S57ScfA1Vrho0;VP0;Vk;S76A5Se9R4R3A5VQ;A3F_;F_;Ftp';Frho';F_;").
Hypothesis Hzero : ltac2:(tb__ "0|1|
S3eS0S4dS32S46Q8A1VF;A2A1Z0M0A3S3S2dS46Q40A1A1S70S45S6bS45S56S57G0A1Vrho0;VP0;Vk;S76A5Se4R2R1A5VQ;A3Ftp';Frho';F_;").

Definition J0s (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S2dS5cA1S5dS3fS56S57Z0A1Vrho0;VP0;Vk;S76Vrho1;R3R2R1A9S3eS0S47G0S4R4P13A2A2Z10000A3A2Lmd;Ltr;Lt;Lr;").
Definition J1k (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S2dS5cA1S5dS3fS56S57ScfA1Vrho0;VP0;Vk;S76Vrho1;R3R2R1A9S3eS0S47G0S4R4P64A2A2ScfA3A2Lmd;Ltr;Lt;Lr;").
Definition J1h (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S2dS5cA1S5dS3fS56S57ScfA1Vrho0;VP0;Vk;S76Vrho1;R3R2R1A9S3fS3eS0S47G0S4R4P65A2A2ScfA3S3eS0S47G0S4R4P64A2A2S100VF;A1A3A2A2Lmd;Ltr;Lt;Lr;").

Lemma nd_Z_NF : ltac2:(tb__ "0|0|
S3eS31S98S8aS76A2S30A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma J0s_stable : ltac2:(tb__ "0|0|
S3S6cS45S8aSd0R1A1A3Frho1;").
Proof.
  intros rho1 r r' t tr md md' Hag Hme [HJ Hv]. split.
  - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_Z Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) nd_Z_NF (agree_below_refl _ _) Hme HJ').
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 19%positive ltac:(cbv; reflexivity)). exact Hv.
Qed.
Lemma J1k_stable : ltac2:(tb__ "0|0|
S3S6cS45P65Sd3R1A1A3Frho1;").
Proof.
  intros rho1 r r' t tr md md' Hag Hme [HJ Hv]. split.
  - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_Z Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) nd_Z_NF (agree_below_refl _ _) Hme HJ').
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 100%positive ltac:(cbv; reflexivity)). exact Hv.
Qed.
Lemma J1h_stable : ltac2:(tb__ "0|0|
S3S6cS45P66Sd2R1A1A3Frho1;").
Proof.
  intros rho1 r r' t tr md md' Hag Hme (HJ & Hv & Hh). split; [|split].
  - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_Z Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) nd_Z_NF (agree_below_refl _ _) Hme HJ').
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 101%positive ltac:(cbv; reflexivity)). exact Hv.
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 100%positive ltac:(cbv; reflexivity)). exact Hh.
Qed.

Lemma s0_bs : ltac2:(tb__ "0|0|
S3S3eS0S47Q40S4R1P13A2A2Z10000A3S3eS2dS46Q8A1A1S12dSc6R2VF;S3Z0L_;R2A1A4Sd1A3F_;Fr;").
Proof.
  intros r Hv. unfold rbA_bs, BS0. rewrite rd_H12. change (eval r vC) with (rw r 19%positive). rewrite Hv. reflexivity.
Qed.
Lemma J0s_fd : ltac2:(tb__ "0|2|
S3S3S2dS46Q40M0A1A1S2dS5cA1S5dSd0R5R4R3R2R1A5S3fS3eS34S5eA1S61S63R2A1S48G0Z3A2A2S33S5eS64Vp3;S48G0S3Z0L_;R5A1A2A2A2A3S3eS34S2dS46Q8A1A1M1A1S120S5fR2A1Vp3;A2S33G1VF;A2A3A2F_;Fmd;Ftr;Ft;Fr;Frho1;").
Proof.
  intros rho1 r t tr md [HJ _]. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & HX). rewrite Hfds. split; [apply HFDS3 | apply HMDXfs; exact HX].
Qed.
Lemma J0s_Kk : ltac2:(tb__ "0|1|
S3S3S2dS46Q40A1A1S2dS5cA1S5dSd0R5R4R3R2R1A5Sd3R6S12fSc6R5VF;S3Z0L_;R5A1M0A4R4R3S12eSc6R5Vp3;VF;G0R2A6A5F_;Fmd;Ftr;Ft;Fr;Frho1;").
Proof.
  intros rho1 r t tr md [HJ Hv]. cbn beta. pose proof BS0_len as BL. split.
  - unfold rbA_md'. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & HX).
    eapply JR_refds; [|exact HJ]. rewrite Hfds. rewrite (s0_bs r Hv). unfold len_word. rewrite BL. unfold KcR.
    etransitivity; [apply HFDSstep; unfold res0; lia | f_equal; lia].
  - unfold rkA_rho'. rewrite rd_next. rewrite rho_set_rw_at. rewrite (s0_bs r Hv). unfold len_word. rewrite BL.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. unfold res0; lia.
Qed.
Lemma J0s_Kh : ltac2:(tb__ "0|1|
S4aZ4S4dS32S46Q8A1VF;A2A1A2S3S3S2dS46Q40A1A1S2dS5cA1S5dSd0R5R4R3R2R1A5Sd2R6S130Sc6R5VF;S3Z0L_;R5A1M0A4R4R3S12eSc6R5Vp3;VF;G0R2A6A5F_;Fmd;Ftr;Ft;Fr;Frho1;F_;").
Proof.
  intros HF4 rho1 r t tr md [HJ Hv]. cbn beta. pose proof BS0_len as BL. split; [|split].
  - unfold rbA_md'. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & HX).
    eapply JR_refds; [|exact HJ]. rewrite Hfds. rewrite (s0_bs r Hv). unfold len_word. rewrite BL. unfold KcR.
    etransitivity; [apply HFDSstep; unfold res0; lia | f_equal; lia].
  - unfold rhA_rho'. rewrite rd_next. cbn [Pos.succ]. rewrite rho_set_rw_at. rewrite (s0_bs r Hv). unfold len_word. rewrite BL.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. unfold res0; lia.
  - unfold rhA_rho'. rewrite rd_next. cbn [Pos.succ]. rewrite rho_set_rw_other by (cbv; discriminate). rewrite rho_set_rw_at. rewrite (s0_bs r Hv).
    unfold BS0. apply hdr_val_word; lia.
Qed.
Lemma J0s_H4 : ltac2:(tb__ "0|1|
S4aZ4S4dS32S46Q8A1M0VF;A2A1A2S3S3S2dS46Q40A1A1S2dS5cA1S5dSd0R5R4R3R2R1A5Sc5U4S32G0S12dSc6R5VF;S3Z0L_;R5A1A4A2A2F_;Fmd;Ftr;Ft;Fr;Frho1;F_;").
Proof. intros HF4 rho1 r t tr md [HJ Hv]. rewrite (s0_bs r Hv). pose proof BS0_len. unfold res0 in *. lia. Qed.

Lemma step_s0 : ltac2:(tb__ "0|0|
S2dS46Q40A1A1S70S45S6bS45S56S57Z0A1Vrho0;VP0;Vk;S76A5SdaVrho0;R1A5VQ;A3Ftp;").
Proof.
  intros tp.
  destruct s0_site as (Hn0 & HLV0 & HnL & HrunL & HerrV & Sp1 & Sp2 & Hn2 & Hset2 & Hs2 & Hcv & HC & HnC & Hs19).
  destruct (node_okb_sound _ _ Hn0) as (N1 & N2 & N3 & _). destruct (node_okb_sound _ _ HnL) as (L1 & L2 & L3 & _).
  destruct (node_okb_sound _ _ HnC) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct s0_call as (Hpb0 & Hpb1 & HimpK & HimpH0 & HimpH1 & Hplt0 & Hplt1 & Hplt2 & HokLk & HTLk & HokLh & HTLh & HnTk & HnTh & HLVk & HLVh).
  destruct (node_okb_sound _ _ HnTk) as (Tk1 & Tk2 & Tk3 & _). destruct (node_okb_sound _ _ HnTh) as (Th1 & Th2 & Th3 & _).

  pose proof run_S0 as R0. rewrite HLV0 in R0.
  eapply JR_run; [exact Hk | exact R0 | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  eapply JR_run; [exact Hk | exact HrunL | exact L2 | exact L1 | exact L3 |].
  intros L rho2 [<-|[]] Hag2. cbn [la_state].

  eapply (etriple_conseq (P := SPA segs (JR (KcR 0) rho0 P0 k nd_Z) C_s0 rho2 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { apply (SPA_errV _ rho2 E_s0 tp w HerrV) in HS. change (errV E_s0) with A0_s0 in HS.
    apply (SPA_split segs _ rho2 A0_s0 0 (SLit (-2256)) _ tp w Sp1) in HS. change (ax_setS A0_s0 (ax_S A1_s0)) with A1_s0 in HS.
    apply (SPA_split segs _ rho2 A1_s0 0 (SLit (-2336)) _ tp w Sp2) in HS. change (ax_setS A1_s0 (ax_S A2_s0)) with A2_s0 in HS.
    destruct (rdsZ_range rho2) as (CR1 & CR2 & CR3).
    apply (SPA_reslice segs _ rho2 A2_s0 (irds A2_s0) _ (O_rdsC (SLit CAP0) []) tp w Hn2 eq_refl eq_refl eq_refl eq_refl ltac:(rewrite Hset2; exact Hs2) CR1 CR2 CR3) in HS.
    rewrite Hset2 in HS. change (ax_setS A2_s0 (ax_S A3_s0)) with A3_s0 in HS.
    unfold carve_chk in Hcv. apply andb_prop in Hcv as [Hcv Cb]. apply andb_prop in Hcv as [Cw Cc]. apply sv_eqb_sound in Cb.
    rewrite <- HC. exact (carveR rho0 P0 k HP0SH (KcR 0) nd_Z A3_s0 rho2 tp w N_rd (ss_next (ax_S A3_s0)) HS Cw (Pos.leb_refl _) Cb Cc). }

  destruct (Z_lt_le_dec (Z.of_nat (length F)) 4) as [HFlt4|HF4].
  -
    apply (pure_callJ_v_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA (KcR 0) (KcR res0) C_s0 Pre_rd s_s0 R_s0 (Posts_rd [] 100) rho2 tp nd_Z
             (J0s rho2) (J1k rho2) Q (KcG_ok _ _)).
    + intros rho3 tp3. apply (read_keep_sum_ex (J0s rho2) (J1k rho2) p3 F (fun _ => 0%Z) (J0s_stable rho2) (J1k_stable rho2)
                               ltac:(intros r; lia) (J0s_fd rho2) (J0s_Kk rho2) rho3 tp3).
    + exact fr_s0.
    + exact cc_s0k.
    + exact M1.
    + exact M3.
    + exact M4.
    +   intros tr ms md Hsm HJ. split; [exact HJ|]. cbn [rho_sub rw]. rewrite Hs19. cbn [eval]. rewrite lit_unsigned. reflexivity.
    +   intros rhoL tr' md' [HJ' _]. exact HJ'.
    +
      intros L rho' rhoL tr' md' HinL Hag' [HJ' Hres] Hpv. destruct HinL as [<-|[]]. cbn [la_state] in Hpv |- *.
      assert (HR : bv_unsigned (rw rho' 100%positive) = res0).
      { pose proof (Hpv 100%positive Hpb0 ltac:(apply Nat.ltb_lt; exact Hplt0)) as E. rewrite HimpK in E. cbn [eval] in E. rewrite <- E. exact Hres. }
      change (ax_add_facts (ss_facts (ax_S C_s0)) (import_postA s_s0 Pre_rd (P_rd [] 100) C_s0 R_s0)) with (T_after Pre_rd C_s0 s_s0 R_s0 (P_rd [] 100)).
      rewrite (proj1 T_s0_eqs).
      apply (errL_Te _ T_s0k' _ rho' tp HokLk (JR_blind (KcR res0) rho0 P0 k NF nd_Z nd_Z_NF)). intros rhoE HrwE _ _. rewrite HTLk.
      rewrite <- HrwE in HR. rename rho' into rhoO'. rename rhoE into rho'.
      pose proof (proj1 run_S0T) as RT. rewrite HLVk in RT.
      eapply JR_run; [exact Hk | exact RT | exact Tk2 | exact Tk1 | exact Tk3 |].
      intros Lf rho5 HinLf Hag5. destruct HinLf as [<-|[<-|[]]]; cbn [la_state].
      *
        destruct s0_contK as (HQ & Kne). pose proof HQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KnQ).
        apply etriple_factsA. intros HF5.
        assert (HR5 : bv_unsigned (rw rho5 100%positive) = res0).
        { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 100%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
        pose proof (resNZ_of_fact rho5 _ _ HF5 Kne) as HNZ. rewrite HR5 in HNZ.
        assert (HF13 : 1 <= Z.of_nat (length F) <= 3) by (unfold res0 in HNZ; lia).
        eapply (etriple_conseq (P := fun w => exists rho6, bv_unsigned (rw rho6 100%positive) = res0 /\ SPA segs (JR (KcR res0) rho0 P0 k nd_Z) QZk rho6 tp w));
          [intros w HS | intros w' Hw'; exact Hw' |].
        { destruct (qz_cleanup (KcR res0) rho0 P0 k [] Ls0k ZKa ZKb QZk rho5 tp w (KcG_ok _ _) lit_cells_nil HQ HP0SH HS) as (rho6 & E6 & HS6).
          exists rho6. split; [rewrite E6; exact HR5 | exact HS6]. }
        apply etriple_ex. intros rho6.
        apply (triple_pre _ _ (bv_unsigned (rw rho6 100%positive) = res0)); [intros w [H _]; exact H | intros HR6].
        eapply (etriple_conseq (P := SPA segs (JR (KcR res0) rho0 P0 k nd_Z) QZk rho6 tp)); [intros w [_ HS]; exact HS | intros w' Hw'; exact Hw' |].
        exact (HcopyK HF13 rho6 tp HR6).
      *
        destruct s0_contZ as (HQ & KeqZ).
        apply etriple_factsA. intros HF5.
        assert (HR5 : bv_unsigned (rw rho5 100%positive) = res0).
        { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 100%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
        pose proof (resZ_of_fact rho5 _ _ HF5 KeqZ) as HZ0. rewrite HR5 in HZ0.
        assert (HF0 : Z.of_nat (length F) = 0) by (unfold res0 in HZ0; lia).
        assert (Eres : res0 = 0) by (unfold res0; lia).
        eapply (etriple_conseq (P := fun w => exists rho6, SPA segs (JR (KcR 0) rho0 P0 k nd_Z) HcZ rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
        { destruct (qz_cleanup (KcR res0) rho0 P0 k [] Lc0k ZCa ZCb HcZ rho5 tp w (KcG_ok _ _) lit_cells_nil HQ HP0SH HS) as (rho6 & _ & HS6).
          exists rho6. rewrite Eres in HS6. exact HS6. }
        apply etriple_ex. intros rho6. apply (Hzero HF0).
  -
    apply (pure_callJ_v_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA (KcR 0) (KcR res0) C_s0 Pre_rd s_s0 R_s0 (Posts_rd hc 101) rho2 tp nd_Z
             (J0s rho2) (J1h rho2) Q (KcG_ok _ _)).
    + intros rho3 tp3. apply (read_hdr_sum_ex (J0s rho2) (J1h rho2) p3 F (fun _ => 0%Z) (J0s_stable rho2) (J1h_stable rho2)
                               ltac:(intros r; lia) (J0s_fd rho2) (J0s_Kh HF4 rho2) (J0s_H4 HF4 rho2) rho3 tp3).
    + exact fr_s0.
    + exact cc_s0h.
    + exact M1.
    + exact M3.
    + exact M4.
    +   intros tr ms md Hsm HJ. split; [exact HJ|]. cbn [rho_sub rw]. rewrite Hs19. cbn [eval]. rewrite lit_unsigned. reflexivity.
    +   intros rhoL tr' md' [HJ' _]. exact HJ'.
    +
      intros L rho' rhoL tr' md' HinL Hag' (HJ' & Hres & Hhw) Hpv. destruct HinL as [<-|[]]. cbn [la_state] in Hpv |- *.
      assert (HR : bv_unsigned (rw rho' 101%positive) = res0).
      { pose proof (Hpv 101%positive Hpb1 ltac:(apply Nat.ltb_lt; exact Hplt2)) as E. rewrite HimpH1 in E. cbn [eval] in E. rewrite <- E. exact Hres. }
      assert (HH : bv_unsigned (rw rho' 100%positive) = hdr_word F).
      { pose proof (Hpv 100%positive Hpb0 ltac:(apply Nat.ltb_lt; exact Hplt1)) as E. rewrite HimpH0 in E. cbn [eval] in E. rewrite <- E. exact Hhw. }
      change (ax_add_facts (ss_facts (ax_S C_s0)) (import_postA s_s0 Pre_rd (P_rd hc 101) C_s0 R_s0)) with (T_after Pre_rd C_s0 s_s0 R_s0 (P_rd hc 101)).
      rewrite (proj1 (proj2 T_s0_eqs)).
      apply (errL_Te _ T_s0h' _ rho' tp HokLh (JR_blind (KcR res0) rho0 P0 k NF nd_Z nd_Z_NF)). intros rhoE HrwE _ _. rewrite HTLh.
      rewrite <- HrwE in HR, HH. rename rho' into rhoO'. rename rhoE into rho'.
      pose proof (proj2 run_S0T) as RT. rewrite HLVh in RT.
      eapply JR_run; [exact Hk | exact RT | exact Th2 | exact Th1 | exact Th3 |].
      intros Lf rho5 HinLf Hag5. destruct HinLf as [<-|[<-|[]]]; cbn [la_state].
      *
        destruct s0_contH as (HQ & Hne & _).
        apply etriple_factsA. intros HF5.
        assert (HR5 : bv_unsigned (rw rho5 101%positive) = res0).
        { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 101%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
        assert (HH5 : bv_unsigned (rw rho5 100%positive) = hdr_word F).
        { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 100%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HH. }
        eapply (etriple_conseq (P := fun w => exists rho6, (bv_unsigned (rw rho6 101%positive) = res0 /\ bv_unsigned (rw rho6 100%positive) = hdr_word F)
                                                         /\ SPA segs (JR (KcR res0) rho0 P0 k nd_Z) QZh rho6 tp w));
          [intros w HS | intros w' Hw'; exact Hw' |].
        { destruct (qz_cleanup (KcR res0) rho0 P0 k hcZ Ls0h ZHa ZHb QZh rho5 tp w (KcG_ok _ _) lit_cells_hcZ HQ HP0SH HS) as (rho6 & E6 & HS6).
          exists rho6. split; [rewrite !E6; split; [exact HR5 | exact HH5] | exact HS6]. }
        apply etriple_ex. intros rho6.
        apply (triple_pre _ _ (bv_unsigned (rw rho6 101%positive) = res0 /\ bv_unsigned (rw rho6 100%positive) = hdr_word F)); [intros w [H _]; exact H | intros [HR6 HH6]].
        eapply (etriple_conseq (P := SPA segs (JR (KcR res0) rho0 P0 k nd_Z) QZh rho6 tp)); [intros w [_ HS]; exact HS | intros w' Hw'; exact Hw' |].
        exact (HcopyH HF4 rho6 tp HR6 HH6).
      *
        destruct s0_contH as (_ & _ & HeqH).
        apply etriple_factsA. intros HF5.
        assert (HR5 : bv_unsigned (rw rho5 101%positive) = res0).
        { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 101%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
        pose proof (resZ_of_fact rho5 _ _ HF5 HeqH) as HZ0. rewrite HR5 in HZ0. exfalso. unfold res0 in HZ0. lia.
Qed.
End FirstRead.

Lemma dstZ_ranges : ltac2:(tb__ "0|4|
S3S5S4aS47Q40M0S7R2S101A2A2S102A2S4aS47G0S7R3R2A2A2Z10000A2S3fS3eS2eS0S0A2SeR4Sf2R3A1M1A2SeR4S1fS101S8Z0A1R3S2fS9A1S1dA5A2A3S3fS4aS15R4G1A2M2S13R4G1A2M3A2S4cS50G3G2A2S4eZ2Z3fA2A2A2A2F_;F_;Fr;Frho;").
Proof.
  intros rho r HB HR. unfold O_dstZ, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  pose proof (urange (eval rho vB)). pose proof (urange (eval rho r)).
  assert (E1 : bv_unsigned (eval rho (add vB (SLit 0))) = bv_unsigned (eval rho vB)).
  { unfold add. rewrite U_add, U_lit. rewrite <- !M64v_eq. change (0 mod 2 ^ 64) with 0. rewrite Z.add_0_r. apply Z.mod_small. lia. }
  assert (E4 : soff rho r = bv_unsigned (eval rho r)) by (unfold soff; rewrite signed_small by lia; reflexivity).
  rewrite !soff_lit_small by lia. rewrite E1, E4. repeat split; lia.
Qed.

Section CopyZk.
Variables (k : Z) (rho0 : valuation) (P0 : valuation -> Prop).
Hypothesis HP0 : ltac2:(tb__ "0|0|
S3VP0;R1A1S3fS3eS0S8fR2P18A2SffA3S8cR2A1A2F_;Fr;").
Hypothesis Hk : 0 <= k.
Let res : Z := Z.of_nat (length F).
Hypothesis HF13 : 1 <= res <= 3.
Let HP0SH : forall r, P0 r -> SH0 r := fun r H => proj1 (proj2 (HP0 r H)).
Let HP0SHR : forall r, P0 r -> SHR r := fun r H => proj2 (HP0 r H).
Hypothesis Hkeep : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Vres;A1R2S95Vres;A1Vk;S75A5SebR2R1A5VQ;A3Ftp';Frho';").

Lemma step_czk : ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S3eS0S47G0S4R2P64A2A2Vres;A3S70S45S6bS45S56S57Vres;A1Vrho0;VP0;Vk;S76A5SeaR3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HR.
  destruct czk_site as (Zfb & HnQf & Sp1 & Sp2 & Sp3 & Hn3 & Hset3 & Hs3 & Sp4 & Hn5 & Hset5 & Hs5 & Hcv & HC1 & HnodeC & HfB & Hf4096 & HnxC & Hs15 & Hs16 & Hs19 & Hs52 & HnodeT & HLVZ).
  destruct s0_contK as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnQ) & _).
  destruct (node_okb_sound _ _ HnQ) as (Q1' & Q2' & Q3' & Q4' & Q5' & Q6').
  destruct (node_okb_sound _ _ HnodeC) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct (node_okb_sound _ _ HnodeT) as (T1 & T2 & T3 & T4 & T5 & T6).
  apply (triple_pre _ _ _ (fun w HS => SPA_JR_facts _ _ _ _ _ _ _ _ _ HS)). intros (HP00 & Hav & HFQ).
  destruct (HP0 _ HP00) as [Q24 QSH].
  assert (HvR : bv_unsigned (eval rho vRes0) <= 65536) by (change (eval rho vRes0) with (rw rho 100%positive); lia).

  eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) QZkf rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { unfold QZkf, ax_add_facts. change (ax_setS QZk (add_facts [SPUle vRes0 (SLit 3)] (ax_S QZk))) with (ax_with_facts QZk ([SPUle vRes0 (SLit 3)] ++ ss_facts (ax_S QZk))).
    apply (SPA_refacts_JA segs); [exact HS | rewrite forallb_app, Zfb; exact Q4' |].
    intros tr md _ HF'. apply Forall_app. split; [|exact HF']. constructor; [|constructor].
    cbn [holds]. change (eval rho vRes0) with (rw rho 100%positive). rewrite HR, U_lit. change (3 mod M64v) with 3. lia. }
  apply etriple_factsA. intros HFQf.
  pose proof (U_SPUle_lit_r rho _ vB ATOPHI HFQf HfB ltac:(unfold ATOPHI; lia)) as HvB.

  eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) C_czk rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs _ rho QZkf 0 (SLit (-2288)) Z1k tp w Sp1 HS) as HS1.
    pose proof (SPA_split segs _ rho (mkAX Z1k (ax_X QZkf) (ax_base QZkf)) 0 (SLit (-2368)) Z2k tp w Sp2 HS1) as HS2.
    pose proof (SPA_split segs _ rho (mkAX Z2k (ax_X QZkf) (ax_base QZkf)) _ vRes0 Z3k tp w Sp3 HS2) as HS3.
    destruct (dstZ_ranges rho vRes0 HvB HvR) as (DR1 & DR2 & DR3).
    pose proof (SPA_reslice segs _ rho (mkAX Z3k (ax_X QZkf) (ax_base QZkf)) _ _ (O_dstZ vRes0) tp w Hn3 eq_refl eq_refl eq_refl eq_refl
                  ltac:(cbn [ax_S]; rewrite Hset3; exact Hs3) DR1 DR2 DR3 HS3) as HS4.
    cbn [ax_S ax_setS ax_X ax_base] in HS4. rewrite Hset3 in HS4.
    pose proof (SPA_split segs _ rho (mkAX Z4k (ax_X QZkf) (ax_base QZkf)) _ (add (SLit RS) vRes0) Z5k tp w Sp4 HS4) as HS5.
    destruct (rds_ranges rho rdsb vRes0 [] (U_rdsb rho) HvR) as (_ & RR1 & _ & _ & RR2 & RR3).
    pose proof (SPA_reslice segs _ rho (mkAX Z5k (ax_X QZkf) (ax_base QZkf)) _ _ (O_rdsC vRes0 []) tp w Hn5 eq_refl eq_refl eq_refl eq_refl
                  ltac:(cbn [ax_S]; rewrite Hset5; exact Hs5) RR1 RR2 RR3 HS5) as HS6.
    cbn [ax_S ax_setS ax_X ax_base] in HS6. rewrite Hset5 in HS6.
    unfold carve_chk in Hcv. apply andb_prop in Hcv as [Hcv Hb6]. apply andb_prop in Hcv as [Hw6 Hc6]. apply sv_eqb_sound in Hb6.
    rewrite <- HC1.
    exact (carveR rho0 P0 k HP0SH (KcR res) nd_Z (mkAX Z6k (ax_X QZkf) (ax_base QZkf)) rho tp w N_mc (ss_next Z6k) HS6 Hw6 (Pos.leb_refl _) Hb6 Hc6). }

  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
               JR (KcR res) rho0 P0 k nd_Z rho t tr md /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 15 16 /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 19 52).
  assert (HstJp : stableA segs NF Jp).
  { intros r r' t tr md md' Hag Hme (HJ & C1 & C2). unfold Jp. split; [|split].
    - destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_Z Ai kc rho rho t tr md md' (Pos.le_refl _) nd_Z_NF (agree_below_refl _ _) Hme HJi).
    - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in C1 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C1.
    - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in C2 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C2. }
  apply (pure_callJ_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA (KcR res) (KcR res) C_czk PreC s_czk R_czk PostsC rho tp nd_Z Jp Jp Q (KcG_ok _ _)).
  - intros rho6 tp6. apply (memcpy_icpt_sum_ex Jp rho6 tp6 HstJp).
    + intros r t tr md (_ & C1 & _). exact C1.
    + intros r t tr md (_ & _ & C2). exact C2.
  - exact fr_czk.
  - exact cc_czk.
  - exact M1.
  - exact M3.
  - exact M4.
  - intros tr ms md Hsm HJ. unfold Jp. split; [exact HJ|].
    assert (HnzB : tnz rho (vB, SLit CAP0)).
    { unfold tnz, vB. cbn [fst eval]. pose proof (holds_fact rho _ _ HFQf Hf4096) as X. unfold vB in X. cbn [holds eval] in X.
      rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
    split.
    + apply band_free_clsZ. rewrite !rw_call'. rewrite Hs15, Hs16.
      exact (JR_tv_band_free _ _ _ _ nd_Z rho tp tr md (vB, SLit CAP0) HJ ltac:(left; reflexivity) HnzB).
    + apply rds_clsZ; rewrite !rw_call'; [rewrite Hs19; apply U_RS | rewrite Hs52, U_lit; change (65536 mod M64v) with 65536; lia].
  - intros rhoL tr' md' (HJ & _). exact HJ.
  -
    intros Lf rho3 HinL Hag3. unfold PostsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.Posts_mc in HinL. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S C_czk)) (import_postA s_czk PreC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.P_icpt C_czk R_czk)) with (T_after PreC C_czk s_czk R_czk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.P_icpt).
    rewrite T_czk_eq.
    assert (HR3 : bv_unsigned (rw rho3 100%positive) = res).
    { destruct Hag3 as (Hv3 & _ & _). rewrite <- (Hv3 100%positive ltac:(rewrite HnxC; apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
    pose proof run_Zk as RZ. rewrite HLVZ in RZ.
    eapply JR_run; [exact Hk | exact RZ | exact T2 | exact T1 | exact T3 |].
    intros L5 rho5 [<-|[]] Hag5. cbn [la_state].
    assert (HR5 : bv_unsigned (rw rho5 100%positive) = res).
    { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 100%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR3. }
    destruct czk_back as (HB & KnodeU & K24 & K30 & K42 & K41 & Ktv & Kbud).
    destruct (node_okb_sound _ _ KnodeU) as (U1 & U2 & U3 & U4 & U5 & U6).
    assert (HvR5 : bv_unsigned (eval rho5 vRes0) <= 65536) by (change (eval rho5 vRes0) with (rw rho5 100%positive); lia).
    eapply (etriple_conseq (P := fun w => exists rho6, bv_unsigned (rw rho6 100%positive) = res /\ SPA segs (JR (KcR res) rho0 P0 k nd_Z) BZku rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
    { destruct (bkz_cleanup _ rho0 P0 k vRes0 [] _ _ _ _ _ rho5 tp w (KcG_ok _ _) lit_cells_nil HB HvR5 HP0SH HS) as (rho6 & Hv6 & HS6).
      exists rho6. split; [rewrite Hv6; exact HR5 | exact HS6]. }
    apply etriple_ex. intros rho6. apply (triple_pre _ _ (bv_unsigned (rw rho6 100%positive) = res)); [intros w [H _]; exact H | intros HR6].
    eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) BZku rho6 tp)); [intros w [_ HS]; exact HS | intros w' Hw'; exact Hw' |].
    eapply (etriple_conseq (P := SPA segs (JR (KcR res) (rho_sub rho6 s_bkZk) (P0R0 res) k nd_R) R0c (rho_sub rho6 s_bkZk) tp));
      [intros w HS | intros w' Hw'; exact Hw' | apply Hkeep].
    apply (JR_reorigin (KcR res) rho0 P0 (P0R0 res) k BZku R0c s_bkZk nd_Z nd_R rho6 tp w ent_bkZk K24 K30 U1 U3 Ktv eq_refl Kbud eq_refl); [|exact HS].
    intros Ai kc HF6 HP06 Hav6 Hkept Hkc HJi. destruct (HP0 _ HP06) as [P24 _].
    unfold P0R0, U. cbn [rho_sub rw]. rewrite K24, K42, K41. unfold vRes0. cbn [eval]. destruct Hav6 as [Hv6 _].
    rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)). unfold U in P24.
    split; [exact P24|]. split; [exact HR6|]. split; [rewrite lit_unsigned; reflexivity|].
    change (rm (rho_sub rho6 s_bkZk)) with (rm rho6). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ HP0SHR HJi).
Qed.
End CopyZk.

Section CopyZh.
Variables (k : Z) (rho0 : valuation) (P0 : valuation -> Prop).
Hypothesis HP0 : ltac2:(tb__ "0|0|
S3VP0;R1A1S3fS3eS0S8fR2P18A2SffA3S8cR2A1A2F_;Fr;").
Hypothesis Hk : 0 <= k.
Hypothesis HF4 : 4 <= Z.of_nat (length F).
Let res : Z := Z.min 65536 (Z.of_nat (length F)).
Let HP0SH : forall r, P0 r -> SH0 r := fun r H => proj1 (proj2 (HP0 r H)).
Let HP0SHR : forall r, P0 r -> SHR r := fun r H => proj2 (HP0 r H).
Hypothesis Hhdr : ltac2:(tb__ "0|0|
S4cVres;Z10000A2S3S2dS46Q40A1A1S70S45S6bS45S56S57Vres;A1R2S91U0Vres;VF;A3Vk;S75A5Sd5R2R1A5VQ;A3Ftp';Frho';F_;").
Hypothesis HgrowZ : ltac2:(tb__ "0|1|
S3eS0Vres;Z10000A3S3S2dS46Q40A1A1S70S45S6bS45S56S57S8bU0M0A1A1R2S93G0VF;A2Vk;S75A5Sd7R2R1A5VQ;A3Ftp';Frho';F_;").

Lemma U_sext32_hdr : ltac2:(tb__ "0|3|
S3S3eS0S47Q40M0S4R1P64M1A2A2S100VF;A1M2A3S3eS0S51S47G0S7R2S25S30Q20S10G1A1A3A2A2S4eZ2Z20A2A2G2A3F_;Frho;").
Proof.
  intros rho HH. cbn [eval ext_low]. change (bv_extract 0 32 (rw rho 100%positive)) with (low32 (rw rho 100%positive)).
  rewrite (sext64_32_mod (low32 (rw rho 100%positive)) 32) by lia. rewrite low32_umod, Z.mod_mod by lia. rewrite HH.
  apply Z.mod_small. unfold hdr_word.
  pose proof (bv_unsigned_in_range 8 (nth 0 F (Z_to_bv 8 0))). pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))).
  pose proof (bv_unsigned_in_range 8 (nth 2 F (Z_to_bv 8 0))). pose proof (bv_unsigned_in_range 8 (nth 3 F (Z_to_bv 8 0))).
  change (bv_modulus 8) with 256 in *. lia.
Qed.

Lemma step_czh : ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S3eS0S47G0S4R2P65A2A2Vres;A3S3eS0S47G0S4R3P64A2A2S100VF;A1A3S70S45S6bS45S56S57Vres;A1Vrho0;VP0;Vk;S76A5Se9R4R3A5VQ;A3F_;F_;Ftp;Frho;").
Proof.
  intros rho tp HR HH.
  destruct czh_site' as (Zfb & HnQf & Sp1 & Sp2 & Sp3 & Hn3 & Hset3 & Hs3 & Sp5 & Sp6 & Mg7 & Hn7 & Hset7 & Hs7 & Hcv & HC1 & HnodeC & HfB & Hf4096 & HnxC
                         & Hs15 & Hs16 & Hs19 & Hs52 & HPosts & HnodeT & HLVZ).
  destruct s0_contH as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnQ) & _).
  destruct (node_okb_sound _ _ HnQ) as (Q1' & Q2' & Q3' & Q4' & Q5' & Q6').
  destruct (node_okb_sound _ _ HnodeC) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct (node_okb_sound _ _ HnodeT) as (T1 & T2 & T3 & T4 & T5 & T6).
  apply (triple_pre _ _ _ (fun w HS => SPA_JR_facts _ _ _ _ _ _ _ _ _ HS)). intros (HP00 & Hav & HFQ).
  destruct (HP0 _ HP00) as [Q24 QSH].
  assert (HvR : bv_unsigned (eval rho vResH) <= 65536) by (change (eval rho vResH) with (rw rho 101%positive); lia).

  eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) QZhf rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { unfold QZhf, ax_add_facts. change (ax_setS QZh (add_facts [SPUle (SLit 4) vResH] (ax_S QZh))) with (ax_with_facts QZh ([SPUle (SLit 4) vResH] ++ ss_facts (ax_S QZh))).
    apply (SPA_refacts_JA segs); [exact HS | rewrite forallb_app, Zfb; exact Q4' |].
    intros tr md _ HF'. apply Forall_app. split; [|exact HF']. constructor; [|constructor].
    cbn [holds]. change (eval rho vResH) with (rw rho 101%positive). rewrite HR, U_lit. change (4 mod M64v) with 4. lia. }
  apply etriple_factsA. intros HFQf.
  pose proof (U_SPUle_lit_r rho _ vB ATOPHI HFQf HfB ltac:(unfold ATOPHI; lia)) as HvB.

  eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) C_czh rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs _ rho QZhf 0 (SLit (-2288)) Z1h tp w Sp1 HS) as HS1.
    pose proof (SPA_split segs _ rho (mkAX Z1h (ax_X QZhf) (ax_base QZhf)) 0 (SLit (-2368)) Z2h tp w Sp2 HS1) as HS2.
    pose proof (SPA_split segs _ rho (mkAX Z2h (ax_X QZhf) (ax_base QZhf)) _ vResH Z3h tp w Sp3 HS2) as HS3.
    destruct (dstZ_ranges rho vResH HvB HvR) as (DR1 & DR2 & DR3).
    pose proof (SPA_reslice segs _ rho (mkAX Z3h (ax_X QZhf) (ax_base QZhf)) _ _ (O_dstZ vResH) tp w Hn3 eq_refl eq_refl eq_refl eq_refl
                  ltac:(cbn [ax_S]; rewrite Hset3; exact Hs3) DR1 DR2 DR3 HS3) as HS4.
    cbn [ax_S ax_setS ax_X ax_base] in HS4. rewrite Hset3 in HS4.
    pose proof (SPA_split segs _ rho (mkAX Z4h (ax_X QZhf) (ax_base QZhf)) _ (SLit (RS + 4)) Z5h tp w Sp5 HS4) as HS5.
    pose proof (SPA_split segs _ rho (mkAX Z5h (ax_X QZhf) (ax_base QZhf)) _ (add (SLit RS) vResH) Z6h tp w Sp6 HS5) as HS6.
    pose proof (SPA_merge segs _ rho (mkAX Z6h (ax_X QZhf) (ax_base QZhf)) _ Z7h tp w Mg7 HS6) as HS7.
    assert (RR : obj_range rho (O_rdsC vResH hcZ) = obj_range rho (O_rdsL vResH (rds_cellsL hcZ))).
    { exact (proj1 (proj2 (rds_ranges rho rdsb vResH hcZ (U_rdsb rho) HvR))). }
    pose proof (SPA_reobj_same_range _ rho (mkAX Z7h (ax_X QZhf) (ax_base QZhf)) _ _ (O_rdsC vResH hcZ) tp w Hn7 ltac:(cbn [ax_S]; rewrite Hset7; exact Hs7) RR
                  (fun ms => rdsL_to_C vResH hcZ rho ms lit_cells_hcZ HvR) HS7) as HS8.
    cbn [ax_S ax_setS ax_X ax_base] in HS8. rewrite Hset7 in HS8.
    unfold carve_chk in Hcv. apply andb_prop in Hcv as [Hcv Hb6]. apply andb_prop in Hcv as [Hw6 Hc6]. apply sv_eqb_sound in Hb6.
    rewrite <- HC1.
    exact (carveR rho0 P0 k HP0SH (KcR res) nd_Z (mkAX Z8h (ax_X QZhf) (ax_base QZhf)) rho tp w N_mc (ss_next Z8h) HS8 Hw6 (Pos.leb_refl _) Hb6 Hc6). }

  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
               JR (KcR res) rho0 P0 k nd_Z rho t tr md /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 15 16 /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ r 19 52).
  assert (HstJp : stableA segs NF Jp).
  { intros r r' t tr md md' Hag Hme (HJ & C1 & C2). unfold Jp. split; [|split].
    - destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_Z Ai kc rho rho t tr md md' (Pos.le_refl _) nd_Z_NF (agree_below_refl _ _) Hme HJi).
    - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in C1 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C1.
    - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.clsZ in C2 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C2. }
  apply (pure_callJ_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA (KcR res) (KcR res) C_czh PreCH s_czh R_czh PostsCH rho tp nd_Z Jp Jp Q (KcG_ok _ _)).
  - intros rho6 tp6. apply (memcpy_icpt_rs_sum_ex Jp rho6 tp6 HstJp).
    + intros r t tr md (_ & C1 & _). exact C1.
    + intros r t tr md (_ & _ & C2). exact C2.
  - exact fr_czh.
  - exact cc_czh.
  - exact M1.
  - exact M3.
  - exact M4.
  - intros tr ms md Hsm HJ. unfold Jp. split; [exact HJ|].
    assert (HnzB : tnz rho (vB, SLit CAP0)).
    { unfold tnz, vB. cbn [fst eval]. pose proof (holds_fact rho _ _ HFQf Hf4096) as X. unfold vB in X. cbn [holds eval] in X.
      rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
    split.
    + apply band_free_clsZ. rewrite !rw_call'. rewrite Hs15, Hs16.
      exact (JR_tv_band_free _ _ _ _ nd_Z rho tp tr md (vB, SLit CAP0) HJ ltac:(left; reflexivity) HnzB).
    + apply rds_clsZ; rewrite !rw_call'; [rewrite Hs19; apply U_RS | rewrite Hs52, U_lit; change (65536 mod M64v) with 65536; lia].
  - intros rhoL tr' md' (HJ & _). exact HJ.
  -
    intros Lf rho3 HinL Hag3. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S C_czh)) (import_postA s_czh PreCH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs.P_icpt C_czh R_czh)) with (T_after PreCH C_czh s_czh R_czh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs.P_icpt).
    rewrite T_czh_eq.
    assert (HR3 : bv_unsigned (rw rho3 101%positive) = res).
    { destruct Hag3 as (Hv3 & _ & _). rewrite <- (Hv3 101%positive ltac:(rewrite HnxC; apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
    assert (HH3 : bv_unsigned (rw rho3 100%positive) = hdr_word F).
    { destruct Hag3 as (Hv3 & _ & _). rewrite <- (Hv3 100%positive ltac:(rewrite HnxC; apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HH. }
    pose proof run_Zh as RZ. rewrite HLVZ in RZ.
    eapply JR_run; [exact Hk | exact RZ | exact T2 | exact T1 | exact T3 |].
    intros L5 rho5 HinL5 Hag5.
    assert (HR5 : bv_unsigned (rw rho5 101%positive) = res).
    { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 101%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR3. }
    assert (HH5 : bv_unsigned (rw rho5 100%positive) = hdr_word F).
    { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 100%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HH3. }
    assert (HvR5 : bv_unsigned (eval rho5 vResH) <= 65536) by (change (eval rho5 vResH) with (rw rho5 101%positive); lia).
    apply etriple_factsA. intros HF5.
    destruct HinL5 as [<-|[<-|[]]]; cbn [la_state] in *.
    +
      destruct czh_grow as (HB & Feq & Gdiff & Gwf & Gnx & Gset & GnE & G24 & G30 & G41 & G45 & Gtv & Gbud).
      destruct (node_okb_sound _ _ GnE) as (E1 & E2 & E3 & E4 & E5 & E6).
      pose proof (proj1 (holds_beq _ _ _) (holds_fact rho5 _ _ HF5 Feq)) as W1.
      change (eval rho5 vResH) with (rw rho5 101%positive) in W1. rewrite HR5, U_lit in W1. change (CAP0 mod M64v) with 65536 in W1.
      eapply (etriple_conseq (P := fun w => exists rho6, (bv_unsigned (rw rho6 101%positive) = res /\ bv_unsigned (rw rho6 100%positive) = hdr_word F)
                                                  /\ SPA segs (JR (KcR res) rho0 P0 k nd_Z) E_mZ rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (bkz_cleanup _ rho0 P0 k vResH hcZ _ _ _ _ _ rho5 tp w (KcG_ok _ _) lit_cells_hcZ HB HvR5 HP0SH HS) as (rho6 & Hv6 & HS6).
        exists rho6. split; [rewrite !Hv6; split; [exact HR5 | exact HH5] | exact HS6]. }
      apply etriple_ex. intros rho6.
      apply (triple_pre _ _ (bv_unsigned (rw rho6 101%positive) = res /\ bv_unsigned (rw rho6 100%positive) = hdr_word F)); [intros w [H _]; exact H | intros [HR6 HH6]].
      eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) E_mZ rho6 tp)); [intros w [_ HS]; exact HS | intros w' Hw'; exact Hw' |].

      eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) E_mZG rho6 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
      { rewrite <- Gset. apply (SPA_restate segs _ rho6 E_mZ (ax_S E_mZG) tp w _ [] Gwf Gdiff Gnx); [| constructor | exact HS].
        unfold diffs_ok. repeat constructor. unfold vResH. cbn [fst snd eval]. apply bv_eq. rewrite HR6, W1, lit_unsigned. reflexivity. }
      rewrite W1. change 65536 with (cap 0).
      eapply (etriple_conseq (P := SPA segs (JR (KcR (cap 0)) (rho_sub rho6 s_GZ) (P0G 0 F) k nd_R) G_cut (rho_sub rho6 s_GZ) tp));
        [intros w HS | intros w' Hw'; exact Hw' | apply (HgrowZ W1)].
      apply (JR_reorigin (KcR (cap 0)) rho0 P0 (P0G 0 F) k E_mZG G_cut s_GZ nd_Z nd_R rho6 tp w ent_GZ G24 G30 E1 E3 Gtv eq_refl Gbud eq_refl); [|exact HS].
      intros Ai kc HF6 HP06 Hav6 Hkept Hkc HJi. destruct (HP0 _ HP06) as [P24 _].
      unfold P0G, U. cbn [rho_sub rw]. rewrite G24, G41, G45. destruct Hav6 as [Hv6 _].
      split; [cbn [eval]; rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)); exact P24|].
      split; [cbn [eval]; rewrite lit_unsigned; reflexivity|].
      split; [exact (U_sext32_hdr rho6 HH6)|].
      change (rm (rho_sub rho6 s_GZ)) with (rm rho6). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ HP0SHR HJi).
    +
      destruct czh_back as (HB & Fne & Ffb & KnodeU & K24 & K30 & K42 & K41 & K45 & Ktv & Kbud).
      destruct (node_okb_sound _ _ KnodeU) as (U1 & U2 & U3 & U4 & U5 & U6).
      pose proof (proj1 (holds_nbeq _ _ _) (holds_fact rho5 _ _ HF5 Fne)) as W1.
      change (eval rho5 vResH) with (rw rho5 101%positive) in W1. rewrite HR5, U_lit in W1. change (CAP0 mod M64v) with 65536 in W1.
      assert (Hlt : res < 65536) by (unfold res in *; lia).
      eapply (etriple_conseq (P := fun w => exists rho6, (bv_unsigned (rw rho6 101%positive) = res /\ bv_unsigned (rw rho6 100%positive) = hdr_word F)
                                                  /\ SPA segs (JR (KcR res) rho0 P0 k nd_Z) (ax_add_facts F_bkZh BZhu) rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (bkz_cleanup _ rho0 P0 k vResH hcZ _ _ _ _ _ rho5 tp w (KcG_ok _ _) lit_cells_hcZ HB HvR5 HP0SH HS) as (rho6 & Hv6 & HS6).
        exists rho6. split; [rewrite !Hv6; split; [exact HR5 | exact HH5]|].
        change (ax_add_facts F_bkZh BZhu) with (ax_with_facts BZhu (F_bkZh ++ ss_facts (ax_S BZhu))).
        apply (SPA_refacts_JA segs); [exact HS6 | exact U4 |].
        intros tr md HJ HF6. apply Forall_app. split; [|exact HF6]. unfold F_bkZh. constructor; [|constructor].
        cbn [holds]. unfold add. rewrite U_add, !U_lit. change (eval rho6 vResH) with (rw rho6 101%positive). rewrite Hv6, HR5, <- !M64v_eq.
        change (1 mod 2 ^ 64) with 1. change (CAP0 mod 2 ^ 64) with 65536. rewrite Z.mod_small; lia. }
      apply etriple_ex. intros rho6.
      apply (triple_pre _ _ (bv_unsigned (rw rho6 101%positive) = res /\ bv_unsigned (rw rho6 100%positive) = hdr_word F)); [intros w [H _]; exact H | intros [HR6 HH6]].
      eapply (etriple_conseq (P := SPA segs (JR (KcR res) rho0 P0 k nd_Z) (ax_add_facts F_bkZh BZhu) rho6 tp)); [intros w [_ HS]; exact HS | intros w' Hw'; exact Hw' |].
      eapply (etriple_conseq (P := SPA segs (JR (KcR res) (rho_sub rho6 s_bkZh) (P0R1 0 res F) k nd_R) R1c (rho_sub rho6 s_bkZh) tp));
        [intros w HS | intros w' Hw'; exact Hw' | apply (Hhdr Hlt)].
      apply (JR_reorigin (KcR res) rho0 P0 (P0R1 0 res F) k (ax_add_facts F_bkZh BZhu) R1c s_bkZh nd_Z nd_R rho6 tp w ent_bkZh K24 K30 U1 U3 Ktv eq_refl Kbud eq_refl); [|exact HS].
      intros Ai kc HF6 HP06 Hav6 Hkept Hkc HJi. destruct (HP0 _ HP06) as [P24 _].
      unfold P0R1, U. cbn [rho_sub rw]. rewrite K24, K42, K41, K45. destruct Hav6 as [Hv6 _].
      split; [cbn [eval]; rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)); exact P24|].
      split; [unfold vResH; cbn [eval]; exact HR6|].
      split; [cbn [eval]; rewrite lit_unsigned; reflexivity|].
      split; [exact (U_sext32_hdr rho6 HH6)|].
      change (rm (rho_sub rho6 s_bkZh)) with (rm rho6). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ HP0SHR HJi).
Qed.
End CopyZh.

Section CloseZ.
Variables (k : Z) (rho0 : valuation) (P0 : valuation -> Prop).
Hypothesis Hk : 0 <= k.
Hypothesis Hsh : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;S76A5Se6R2R1A5VQ;A3Ftp';Frho';").
Lemma step_closeZ : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Z0A1Vrho0;VP0;Vk;S76A5Se4R2R1A5VQ;A3Ftp;Frho;").
Proof.
  destruct closeZ_facts as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  pose proof (proj2 (proj2 run_c)) as R1. rewrite C1 in R1. pose proof (proj2 (proj2 run_h)) as R2. rewrite C7 in R2.
  apply (step_close 0 k rho0 P0 nd_Z HcZ E_clZ _ Hk C0 R1 C2 C3 C4 C5 C6 R2).
  intros Lf [<-|[]] rho' tp'; cbn [la_state]; apply Hsh.
Qed.
End CloseZ.

Lemma P0R0_SHR : ltac2:(tb__ "0|0|
S0S3S95R2R1A2S8cR2A1F_;Fr;Flen;").
Proof. intros len r (_ & _ & _ & H). exact H. Qed.
Lemma P0RD0_SHR : ltac2:(tb__ "0|0|
S0S0S3S94R3R2R1A3S8cR2A1F_;Fr;Fwant;Flen;").
Proof. intros len want r [H _]. eapply P0R0_SHR; exact H. Qed.

Section Head0.
Variables (len k : Z) (rho0 : valuation).
Let P0 := P0R0 len.
Hypothesis Hlen : 1 <= len <= 3.
Hypothesis Hk : 0 <= k.
Hypothesis Hrd : ltac2:(tb__ "0|1|
S0S3S2dS46Q40A1A1S3fS4aZ1R3A2S4aR3Z10000M0A2A2S4aS4bVlen;R4A2G0A2S70S45S6bS45S56S57Vlen;A1R4S94Vlen;R5A2Vk;S75A5SecR4R3A5VQ;A3F_;F_;Ftp';Frho';Fwant;").

Lemma step_head0 : ltac2:(tb__ "0|0|
S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5SebVrho0;R1A5VQ;A3Ftp;").
Proof.
  intros tp.
  destruct head0_facts as (Hnode & HLVR & Na & Nb & Ea & A24 & A30 & A42 & A41 & A49 & Atv & Abud & Fa1 & Fb1).
  destruct (node_okb_sound _ _ Hnode) as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (node_okb_sound _ _ Na) as (Na1 & Na2 & Na3 & _).
  pose proof run_R0 as RR. rewrite HLVR in RR.
  eapply JR_run; [exact Hk | exact RR | exact N2 | exact N1 | exact N3 |].
  intros L rho1 HinL Hag1.
  apply (triple_pre _ _ _ (fun w HS => SPA_JR_facts _ _ _ _ _ _ _ _ _ HS)). intros ((Q24 & Q42 & Q41 & QSH) & Hav & HF).
  rewrite <- (U_agree rho0 rho1 42%positive Hav ltac:(cbv; reflexivity)) in Q42.
  rewrite <- (U_agree rho0 rho1 41%positive Hav ltac:(cbv; reflexivity)) in Q41. unfold U in Q42, Q41.
  assert (USUB : bv_unsigned (eval rho1 (SAlu ALU_SUB vCap vLen)) = 65536 - len).
  { rewrite U_sub. change (eval rho1 vCap) with (rw rho1 41%positive). change (eval rho1 vLen) with (rw rho1 42%positive).
    rewrite Q41, Q42, <- M64v_eq. apply Z.mod_small. lia. }
  destruct HinL as [<-|[<-|[]]]; cbn [la_state] in *.
  -
    eapply (etriple_conseq (P := SPA segs (JR (KcR len) (rho_sub rho1 s_RDa) (P0RD0 len (65536 - len)) k nd_R) RD0 (rho_sub rho1 s_RDa) tp));
      [intros w HS | intros w' Hw'; exact Hw' | apply (Hrd (65536 - len)); lia].
    apply (JR_reorigin (KcR len) rho0 P0 (P0RD0 len (65536 - len)) k Ra0 RD0 s_RDa nd_R nd_R rho1 tp w Ea A24 A30 Na1 Na3 Atv eq_refl Abud eq_refl); [|exact HS].
    intros Ai kc HF6 HP0 Hav6 Hkept Hkc HJi. destruct HP0 as (P24 & P42 & P41 & PSH).
    unfold P0RD0, P0R0, U. cbn [rho_sub rw]. rewrite A24, A49, A42, A41. cbn [eval]. destruct Hav6 as [Hv6 _].
    rewrite <- (Hv6 24%positive ltac:(cbv; reflexivity)).
    unfold U in P24. split; [|exact USUB]. split; [exact P24|]. split; [exact Q42|]. split; [exact Q41|].
    change (rm (rho_sub rho1 s_RDa)) with (rm rho1). exact (SHR_now _ _ _ _ _ _ _ _ _ _ _ (P0R0_SHR len) HJi).
  -
    pose proof (proj1 (holds_nbltu _ _ _) (holds_fact rho1 _ _ HF Fb1)) as W1. rewrite USUB, U_lit in W1. change (65536 mod M64v) with 65536 in W1. exfalso. lia.
Qed.
End Head0.

Section ReadStep0.
Variables (len want k : Z) (rho0 : valuation).
Let P0 := P0RD0 len want.
Hypothesis Hlen : 1 <= len <= 3.
Hypothesis Hlw : len + want <= 65536.
Hypothesis Hw : 1 <= want <= 65536.
Hypothesis HlenF : ltac2:(tb__ "0|0|
S3eS0Vlen;S4dS32S46Q8A1VF;A2A1A3").
Hypothesis Hk : 0 <= k.
Hypothesis Hclose : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5Se2R2R1A5VQ;A3Ftp';Frho';").

Definition J0r0 (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S2dS5cA1S5dS3fS56S57Vlen;A1Vrho0;VP0;Vk;S75Vrho1;R3R2R1A9S3eS0S47G0S4R4P13A2A2Vwant;A3A2Lmd;Ltr;Lt;Lr;").
Definition J1r0 (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S3S2dS46Q40M0A1A1S2dS5cA1S5dS3fS56S57Vlen;A1Vrho0;VP0;Vk;S75Vrho1;R3R2R1A9S3eS0S47G0S4R4P64A2A2Z0A3A2Lmd;Ltr;Lt;Lr;").

Lemma J0r0_stable : ltac2:(tb__ "0|0|
S3S6cS45S8aS13bR1A1A3Frho1;").
Proof.
  intros rho1 r r' t tr md md' Hag Hme [HJ Hv]. split.
  - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_R Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) (nd_R_NF) (agree_below_refl _ _) Hme HJ').
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 19%positive ltac:(cbv; reflexivity)). exact Hv.
Qed.
Lemma J1r0_stable : ltac2:(tb__ "0|0|
S3S6cS45P65S13cR1A1A3Frho1;").
Proof.
  intros rho1 r r' t tr md md' Hag Hme [HJ Hv]. split.
  - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk k) PA (KcG_ok _ _) ALA NF nd_R Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) (nd_R_NF) (agree_below_refl _ _) Hme HJ').
  - destruct Hag as (Hv' & _ & _). rewrite <- (Hv' 100%positive ltac:(cbv; reflexivity)). exact Hv.
Qed.

Lemma r0_bs : ltac2:(tb__ "0|1|
S3S3eS0S47Q40S4R1P13A2A2Vwant;A3S3eS2dS46Q8A1M0A1S12dSc6R2VF;Vlen;A4S2fG0A1A3F_;Fr;").
Proof.
  intros r Hv. unfold rbA_bs. rewrite rd_H12. change (eval r vC) with (rw r 19%positive). rewrite Hv.
  rewrite skipn_all2 by lia. apply firstn_nil.
Qed.
Lemma J0r0_fd : ltac2:(tb__ "0|2|
S3S3S2dS46Q40M0A1A1S2dS5cA1S5dS13bR5R4R3R2R1A5S3fS3eS34S5eA1S61S63R2A1S48G0Z3A2A2S33S5eS64Vp3;S48G0S3Vlen;L_;R5A1A2A2A2A3S3eS34S2dS46Q8A1A1M1A1S120S5fR2A1Vp3;A2S33G1VF;A2A3A2F_;Fmd;Ftr;Ft;Fr;Frho1;").
Proof.
  intros rho1 r t tr md [HJ _]. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & HX). rewrite Hfds. split; [apply HFDS3 | apply HMDXfs; exact HX].
Qed.
Lemma J0r0_K : ltac2:(tb__ "0|1|
S3S3S2dS46Q40A1A1S2dS5cA1S5dS13bR5R4R3R2R1A5S13cR6S12fSc6R5VF;S3Vlen;L_;R5A1M0A4R4R3S12eSc6R5Vp3;VF;G0R2A6A5F_;Fmd;Ftr;Ft;Fr;Frho1;").
Proof.
  intros rho1 r t tr md [HJ Hv]. cbn beta. split.
  - unfold rbA_md'. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & HX).
    eapply JR_refds; [|exact HJ]. rewrite Hfds. rewrite (r0_bs r Hv). unfold len_word. cbn [length Z.of_nat].
    etransitivity; [apply HFDSstep; lia | f_equal; lia].
  - unfold rkA_rho'. rewrite rd_next. rewrite rho_set_rw_at. rewrite (r0_bs r Hv). unfold len_word. cbn [length Z.of_nat]. rewrite lit_unsigned. reflexivity.
Qed.

Lemma step_rd0 : ltac2:(tb__ "0|0|
S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5SecVrho0;R1A5VQ;A3Ftp;").
Proof.
  intros tp.
  destruct rd0_site as (Hnode & HerrV & Sp1 & Sp2 & Sp3 & Hn3 & Hset3 & Hs3 & Hcv & HC1 & HnodeC & Hfw).
  destruct (node_okb_sound _ _ Hnode) as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (node_okb_sound _ _ HnodeC) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct rd0_call as (Hs19 & Hs17 & Hs15 & Hs16 & Hpb & Himp & Hplt & HnodeT & HLVT & Hbne).
  destruct (node_okb_sound _ _ HnodeT) as (T1 & T2 & T3 & T4 & T5 & T6).
  eapply JR_run; [exact Hk | exact (proj1 run_RD) | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. intros HF1.
  pose proof (U_SPUle_lit_r rho1 _ vWant 65536 HF1 Hfw ltac:(lia)) as HW1.

  eapply (etriple_conseq (P := SPA segs (JR (KcR len) rho0 P0 k nd_R) C_rd0 rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { apply (SPA_errV _ rho1 E_rd0 tp w HerrV) in HS. fold A0_rd0 in HS.
    apply (SPA_split segs _ rho1 A0_rd0 0 (SLit (-2256)) _ tp w Sp1) in HS. change (ax_setS A0_rd0 (ax_S A1_rd0)) with A1_rd0 in HS.
    apply (SPA_split segs _ rho1 A1_rd0 0 (SLit (-2336)) _ tp w Sp2) in HS. change (ax_setS A1_rd0 (ax_S A2_rd0)) with A2_rd0 in HS.
    apply (SPA_split segs _ rho1 A2_rd0 _ (add (SLit RS) vWant) _ tp w Sp3) in HS. change (ax_setS A2_rd0 (ax_S A3_rd0)) with A3_rd0 in HS.
    destruct (rds_ranges rho1 rdsb vWant [] (U_rdsb rho1) HW1) as (_ & CR1 & _ & _ & CR2 & CR3).
    apply (SPA_reslice segs _ rho1 A3_rd0 (irds A3_rd0) _ (O_rdsC vWant []) tp w Hn3 eq_refl eq_refl eq_refl eq_refl ltac:(rewrite Hset3; exact Hs3) CR1 CR2 CR3) in HS.
    rewrite Hset3 in HS. change (ax_setS A3_rd0 (ax_S A4_rd0)) with A4_rd0 in HS.
    unfold carve_chk in Hcv. apply andb_prop in Hcv as [Hcv Hb6]. apply andb_prop in Hcv as [Hw6 Hc6]. apply sv_eqb_sound in Hb6.
    rewrite <- HC1. apply (carveR rho0 P0 k (fun r H => proj1 (P0RD0_SHR len want r H)) (KcR len) nd_R A4_rd0 rho1 tp w N_rd (ss_next (ax_S A4_rd0)) HS Hw6 (Pos.leb_refl _) Hb6 Hc6). }

  apply (pure_callJ_v_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk k) PA (KcR len) (KcR len) C_rd0 Pre_rd s_rd0 R_rd0 (Posts_rd [] 100) rho1 tp nd_R
           (J0r0 rho1) (J1r0 rho1) Q (KcG_ok _ _)).
  - intros rho2 tp2. apply (read_keep_sum_ex (J0r0 rho1) (J1r0 rho1) p3 F (fun _ => len) (J0r0_stable rho1) (J1r0_stable rho1)
                             ltac:(intros r; lia) (J0r0_fd rho1) (J0r0_K rho1) rho2 tp2).
  - exact fr_rd0.
  - exact cc_rd0k.
  - exact M1.
  - exact M3.
  - exact M4.
  -   intros tr ms md Hsm HJ. split; [exact HJ|].
    cbn [rho_sub rw]. rewrite Hs19. rewrite eval_absorb. change (eval rho1 vWant) with (rw rho1 49%positive).
    destruct (JR_P0 _ _ _ _ _ _ _ _ _ HJ) as [[_ HP49] Hav]. rewrite <- (U_agree rho0 rho1 49%positive Hav ltac:(cbv; reflexivity)) in HP49. exact HP49.
  -   intros rhoL tr' md' [HJ' _]. exact HJ'.
  -
    intros L rho' rhoL tr' md' HinL Hag' [HJ' Hres] Hpv. destruct HinL as [<-|[]]. cbn [la_state] in Hpv |- *.
    assert (HR : bv_unsigned (rw rho' 101%positive) = 0).
    { pose proof (Hpv 100%positive Hpb ltac:(apply Nat.ltb_lt; exact Hplt)) as E. rewrite Himp in E. unfold vRes1 in E. cbn [eval] in E. rewrite <- E. exact Hres. }
    change (ax_add_facts (ss_facts (ax_S C_rd0)) (import_postA s_rd0 Pre_rd (P_rd [] 100) C_rd0 R_rd0)) with (T_after Pre_rd C_rd0 s_rd0 R_rd0 (P_rd [] 100)).
    destruct T_rd_eqs as (ET & _ & EL & _ & HokL & _). rewrite ET.
    apply (errL_Te _ T_rd0k' _ rho' tp HokL (JR_blind (KcR len) rho0 P0 k NF nd_R nd_R_NF)). intros rhoE HrwE _ _. rewrite EL.
    rewrite <- HrwE in HR. rename rho' into rhoO'. rename rhoE into rho'.
    pose proof (proj1 run_T) as RT. rewrite HLVT in RT.
    eapply JR_run; [exact Hk | exact RT | exact T2 | exact T1 | exact T3 |].
    intros Lf rho5 HinLf Hag5. destruct HinLf as [<-|[<-|[]]]; cbn [la_state].
    +
      apply etriple_factsA. intros HF5.
      assert (HR5 : bv_unsigned (rw rho5 101%positive) = 0).
      { destruct Hag5 as (Hv5 & _ & _). rewrite <- (Hv5 101%positive ltac:(apply Pos.ltb_lt; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). exact HR. }
      pose proof (resNZ_of_fact rho5 _ _ HF5 Hbne) as HNZ. exfalso. exact (HNZ HR5).
    +
      destruct rd0_close as (Xa & Kn & Kset & Ks & Xc & Kobjs & Knb & KX & KQ & KnodeQ & Keq & Kfw).
      apply etriple_factsA. intros HF5.
      pose proof (U_SPUle_lit_r rho5 _ vWant 65536 HF5 Kfw ltac:(lia)) as HW5.
      eapply (etriple_conseq (P := fun w => exists rho6, SPA segs (JR (KcR len) rho0 P0 k nd_R) Hc0 rho6 tp w));
        [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct (q_cleanup (KcR len) rho0 P0 k Lcl0 H0a H0b H0c Hc0 rho5 tp w (KcG_ok _ _) Xa Kn Kset Ks eq_refl eq_refl Xc Kobjs Knb KX KQ HW5 (fun r H => proj1 (P0RD0_SHR len want r H)) HS)
          as (rho6 & _ & HS6). exists rho6. exact HS6. }
      apply etriple_ex. intros rho6. apply Hclose.
Qed.
End ReadStep0.

Section Close0.
Variables (len k : Z) (rho0 : valuation) (P0 : valuation -> Prop).
Hypothesis Hk : 0 <= k.
Hypothesis Hsh : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S58Vrho0;VP0;Vk;S75A5Se5R2R1A5VQ;A3Ftp';Frho';").
Lemma step_close0 : ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S70S45S6bS45S56S57Vlen;A1Vrho0;VP0;Vk;S75A5Se2R2R1A5VQ;A3Ftp;Frho;").
Proof.
  destruct close0_facts as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  pose proof (proj1 (proj2 run_c)) as R1. rewrite C1 in R1. pose proof (proj1 (proj2 run_h)) as R2. rewrite C7 in R2.
  apply (step_close len k rho0 P0 nd_R Hc0 E_cl0 _ Hk C0 R1 C2 C3 C4 C5 C6 R2).
  intros Lf [<-|[]] rho' tp'; cbn [la_state]; apply Hsh.
Qed.
End Close0.

Section RFile.

Hypothesis HSref : ltac2:(tb__ "0|1|
S4aS131S4dS32S46Q8A1M0VF;A2A1A2S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafG0S5cS60Sc2A1S132A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;F_;").
Hypothesis HSsh : ltac2:(tb__ "0|1|
S4cS4dS32S46Q8A1M0VF;A2A1Z6A2S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafG0S5cS60Sc2A1S134A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;F_;").
Hypothesis HSov : ltac2:(tb__ "0|3|
S3fS4aZ6M0S4dS32S46Q8A1M1VF;A2A1M2A2S4cG2S4bG0S103VF;A1A2A2A2S71S5dVMDX;R1A1S3eS2dS5cA1S72R3A1S35S5cVT0;S35S5cSafG1S5cS60Sc2A1S133A4S37S5cS62S48Q40Z2A2S5fR2A1A2S2fS5cA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;F_;").

Hypothesis HT : ltac2:(tb__ "0|1|
S3fS4aS4bZ6S103VF;A1A2S4dS32S46Q8A1VF;A2A1M0A2S4cG0S131A2A2S3S3S2dS46Q40A1A1S70S45S6bS45SfcVAInv;VCST;VXGL;R3VF;VT0;S5bVPA;U0S107AaS106R2R1A5VQ;A3Ftp;Frho;FrhoT;F_;").

Lemma HTsh0_ok : ltac2:(tb__ "0|0|
S0S0S0S3S3fS4aZ1R4A2S4aR4Z3A2A2S3eS0R5S4dS32S46Q8A1VF;A2A1A3S4aSb3R4A2S3S2dS46Q40A1A1S70S45S6bS45S56S58R6S94R9R8A2R7S75A5Se5R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;Frho0;Fk;Fwant;Flen;").
Proof.
  intros len want k rho0 Hlen HlenF Hk rho tp.
  exact (tail_free vB vCap bd_R 0x21441 31 0x21440 0x40 Lsh0 E_sh0 C_sh0 T_sh0 U_sh0 V_sh0 W_sh0 F_sh0 CF_sh0 TF_sh0 X_sh0 CX_sh0 s_sh0 sF_sh0 R_sh0 RF_sh0
           msg_short fw_in_sh MSGB_short blk_sh (P0RD0 len want) k rho0 (P0RD0_SHR len want) Hk eq_refl sh0_facts (HSsh ltac:(lia)) rho tp).
Qed.
Lemma HTshZ_ok : ltac2:(tb__ "0|0|
S0S3S3OF_;S3R2R1A1S8cR2A1F_;Fr;S3eS0S4dS32S46Q8A1VF;A2A1Z0A3S4aSb3R5A2S3S2dS46Q40A1A1S70S45S6bS45S56S58R7R6R8S76A5Se6R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;FP0;Frho0;Fk;").
Proof.
  intros k rho0 P0 HP0 HF0 Hk rho tp.
  exact (tail_free vB (SLit CAP0) bd_Z 0x21441 31 0x21440 0x40 LshZ E_shZ C_shZ T_shZ U_shZ V_shZ W_shZ F_shZ CF_shZ TF_shZ X_shZ CX_shZ s_shZ sF_shZ R_shZ RF_shZ
           msg_short fw_in_sh MSGB_short blk_sh P0 k rho0 HP0 Hk eq_refl shZ_facts (HSsh ltac:(lia)) rho tp).
Qed.

Lemma K_T_pos : 1 <= K_T.
Proof. vm_compute. intros H; discriminate H. Qed.
Lemma V_T_nonneg : 0 <= V_T.
Proof. vm_compute. intros H; discriminate H. Qed.

Lemma r_file_core : ltac2:(tb__ "0|0|
S3S3OF_;S3R2R1A1S3fS3eS0S8fR2P18A2SffA3S8cR2A1A2F_;Fr;S2dS46Q40A1A1S70S45S6bS45S56S57Z0A1R4R3S92S76A5SdaR4R1A5VQ;A3Ftp;F_;FP0;Frho;").
Proof.
  intros rho P0 HP0 tp. pose proof K_T_pos as KT1.
  assert (HK0 : 0 <= K0) by (unfold K0, KU; lia).
  assert (LP1 : forall g len k rho0 tp0, (g <= 10)%nat -> 4 <= len < cap g -> len <= Z.of_nat (length F) -> KU * K_T + 2 * KU * (10 - Z.of_nat g) <= k ->
            etriple segs (SPA segs (JR (KcR len) rho0 (P0R1 g len F) k nd_R) R1c rho0 tp0) Q).
  { intros g len k rho0 tp0 Hg Hlen HlenF Hk.
    apply (loop1 (KU * K_T) ltac:(unfold KU; lia) ltac:(lia)); try assumption.
    + intros g' len' want k' rho0' Hg' Hlen' HlenF' Hw' Hk'. apply (step_T g' len' want k' rho0' Hg' Hlen' HlenF' Hk' HT).
    + intros g' len' want k' rho0' Hg' Hlen' HlenF' Hw' Hk'. apply (HTsh_ok HSsh g' len' want k' rho0' Hg' Hlen' HlenF' Hw'); unfold KU in *; lia.
    + intros g' len' want k' rho0' Hg' Hlen' HlenF' Hw' Hk'. apply (HTov_ok HSov g' len' want k' rho0' Hg' Hlen' HlenF' Hw'); unfold KU in *; lia.
    + intros g' len' want res k' rho0' Hg' Hlen' Hres Hw' Hlc H26 HlenF' Hk'. apply (HTref_ok HSref g' len' want res k' rho0' Hg' Hlen' Hres Hw' Hlc H26 HlenF'); unfold KU in *; lia.
  }
  apply (step_s0 K0 rho P0 HP0 HK0).
  -
    intros HF13 rho' tp' HR.
    assert (Eres : res0 = Z.of_nat (length F)) by (unfold res0; lia). rewrite Eres in HR |- *.
    apply (step_czk K0 rho P0 HP0 HK0 HF13); [|exact HR]. intros rho2 tp2.
    apply (step_head0 (Z.of_nat (length F)) K0 rho2 ltac:(lia) HK0). intros want rho3 tp3 Hw Hlw.
    eapply (step_rd0 (Z.of_nat (length F)) want K0 rho3); try exact HK0; try lia. intros rho4 tp4.
    apply (step_close0 (Z.of_nat (length F)) K0 rho3 (P0RD0 (Z.of_nat (length F)) want) HK0). intros rho5 tp5.
    apply (HTsh0_ok (Z.of_nat (length F)) want K0 rho3 ltac:(lia) eq_refl). unfold K0, KU. lia.
  -
    intros HF4 rho' tp' HR HH.
    apply (step_czh K0 rho P0 HP0 HK0 HF4); [| |exact HR|exact HH].
    + intros Hlt rho2 tp2. apply (LP1 0%nat); [lia | change (cap 0) with 65536; lia | lia | unfold K0, KU; cbn [Z.of_nat]; lia].
    + intros Heq rho2 tp2.
      apply (grow0 (KU * K_T) ltac:(unfold KU; lia) ltac:(lia)).
      * intros g' len' want k' rho0' Hg' Hlen' HlenF' Hw' Hk'. apply (step_T g' len' want k' rho0' Hg' Hlen' HlenF' Hk' HT).
      * intros g' len' want k' rho0' Hg' Hlen' HlenF' Hw' Hk'. apply (HTsh_ok HSsh g' len' want k' rho0' Hg' Hlen' HlenF' Hw'); unfold KU in *; lia.
      * intros g' len' want k' rho0' Hg' Hlen' HlenF' Hw' Hk'. apply (HTov_ok HSov g' len' want k' rho0' Hg' Hlen' HlenF' Hw'); unfold KU in *; lia.
      * intros g' len' want res k' rho0' Hg' Hlen' Hres Hw' Hlc H26 HlenF' Hk'. apply (HTref_ok HSref g' len' want res k' rho0' Hg' Hlen' Hres Hw' Hlc H26 HlenF'); unfold KU in *; lia.
      * lia.
      * unfold K0, KU. lia.
      * unfold K0, KU. lia.
  -
    intros HF0 rho' tp'.
    apply (step_closeZ K0 rho P0 HK0). intros rho'' tp''.
    apply (HTshZ_ok K0 rho P0 (fun r H => proj2 (HP0 r H)) HF0). unfold K0, KU. lia.
Qed.

Theorem r_file_ex : ltac2:(tb__ "0|1|
S3S2dS46Q40A1A1S70S45S6bS45S97VAInv;VCST;VXGL;S8aS57Z0A1R2S122Vp3;A1S2fS2eS0S0A2M0A1S2fS2eG0S0A2A1Sf8VPA;S124AcS123R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp.
  assert (HP0 : forall r, DrvIfaceR.P0Z p3 r -> U r 24 = TP /\ SHR r).
  { intros r (H24 & HS & _). split; [exact H24 | exact HS]. }

  eapply (etriple_conseq (P := SPA segs (JR (KcR 0) rho (DrvIfaceR.P0Z p3) K0 nd_Z) S_R0 rho tp)); [intros w [Hsm (Ai & kc & HJ)] | intros w' Hw'; exact Hw' |].
  { split; [exact Hsm|]. exists Ai, kc.
    pose proof K_T_pos as KT1. pose proof V_T_nonneg as VT0.
    apply (JAi_rebud (KcR 0) rho (DrvIfaceR.P0Z p3) BX0 (BXk K0) DrvIfaceR.nd_R0 bd_Z Ai kc rho tp); [reflexivity | cbn; lia | cbn [snd bx2 BXk]; unfold K0, KU; lia | reflexivity | | exact HJ].
    intros V Km Kf HB. cbn [nd_bd nd_am DrvIfaceR.nd_R0] in HB |- *. destruct HB as (_ & _ & _ & _ & _ & _ & Hnn & _).
    unfold bxa, BXk, BX0, DrvIfaceR.bd_R0, bd_Z, bsumV, bsumK, bival, BIc, VR, K0. cbn [fst snd bx2 lfval bi_f bi_c bi_v bi_k aval uval].
    split; [unfold bd_nn; apply Forall_cons; [|apply Forall_nil]; unfold bival; cbn [lfval bi_f bi_c]; lia|]. lia. }

  eapply (etriple_conseq (P := SPA segs (JR (KcR 0) rho (DrvIfaceR.P0Z p3) K0 nd_Z) S0f rho tp)); [intros w HS | intros w' Hw'; exact Hw' | apply (r_file_core rho _ HP0)].
  unfold S0f, ax_add_facts. change (ax_setS S_R0 (add_facts [SPAlign 24 3] (ax_S S_R0))) with (ax_with_facts S_R0 ([SPAlign 24 3] ++ ss_facts (ax_S S_R0))).
  apply (SPA_refacts_JA segs); [exact HS | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros tr md HJ HF. apply Forall_app. split; [|exact HF]. constructor; [|constructor].
  assert (X : holds rho (SPEq vTP (SLit TP))) by (eapply holds_mem; [exact HF | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]).
  cbn [holds] in X |- *. unfold vTP in X. cbn [eval] in X. rewrite X. rewrite lit_unsigned. split; [lia | reflexivity].
Qed.
End RFile.

Lemma r_entry_glue : ltac2:(tb__ "0|3|
S2dS2eS46Q40A1M0S5eA2A1S3S3OF_;S71S2dG0A1S6bS45S97VAInv;VCST;VXGL;S8aS59R5S2fS5cA1M1A2R4R3S2fS2eS0S0A2M2A1S2fS2eG2S0A2A1Sf8VPA;S124AcS123R4R1R2A6S6bS45S56S59R6G1A2R5R4S92S76A5SdaR5R2R3A6F_;Ftp;Fw;FP0;Frho;Ffds;").
Proof.
  intros fds rho P0 w tp HS0. pose proof K_T_pos as KT1. pose proof V_T_nonneg as VT0.
  assert (HS1 : SPA segs (JR (KcG fds []) rho P0 K0 nd_Z) S_R0 rho tp w).
  { destruct HS0 as [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
    apply (JAi_rebud (KcG fds []) rho P0 BX0 (BXk K0) DrvIfaceR.nd_R0 bd_Z Ai kc rho tp); [reflexivity | cbn; lia | cbn [snd bx2 BXk]; unfold K0, KU; lia | reflexivity | | exact HJ].
    intros V Km Kf HB. cbn [nd_bd nd_am DrvIfaceR.nd_R0] in HB |- *. destruct HB as (_ & _ & _ & _ & _ & _ & Hnn & _).
    unfold bxa, BXk, BX0, DrvIfaceR.bd_R0, bd_Z, bsumV, bsumK, bival, BIc, VR, K0. cbn [fst snd bx2 lfval bi_f bi_c bi_v bi_k aval uval].
    split; [unfold bd_nn; apply Forall_cons; [|apply Forall_nil]; unfold bival; cbn [lfval bi_f bi_c]; lia|]. lia. }
  unfold S0f, ax_add_facts. change (ax_setS S_R0 (add_facts [SPAlign 24 3] (ax_S S_R0))) with (ax_with_facts S_R0 ([SPAlign 24 3] ++ ss_facts (ax_S S_R0))).
  apply (SPA_refacts_JA segs); [exact HS1 | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros tr md HJ HF. apply Forall_app. split; [|exact HF]. constructor; [|constructor].
  assert (X : holds rho (SPEq vTP (SLit TP))) by (eapply holds_mem; [exact HF | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]).
  cbn [holds] in X |- *. unfold vTP in X. cbn [eval] in X. rewrite X. rewrite lit_unsigned. split; [lia | reflexivity].
Qed.

Section RDir.
Variable fdsD : list (word * FdEntry).
Hypothesis HD3 : ltac2:(tb__ "0|0|
S3eS34S5eA1S61VfdsD;S48Q40Z3A2A2S33S5eS68A2A3").
Let KcD : KcA := KcG fdsD [].

Hypothesis HTrderr : ltac2:(tb__ "0|0|
S3S3OF_;S3S2dS46Q40A1A1S3R4R1A1S122Vp3;R2A2F_;Fr;S70S45S6bS45S56VKcD;R5R4S92S76A5S15dR3R2A5VQ;A3F_;Ftp;Frho;FP0;Frho0;").

Definition J0d (P0 : valuation -> Prop) (rho0 rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S3S2dS46Q40A1A1S2dS5cA1S5dS56VKcD;Vrho0;VP0;S92S76Vrho1;R3R2R1A9Lmd;Ltr;Lt;L_;").
Lemma J0d_stable : ltac2:(tb__ "0|0|
S3OF_;S3S3S1S6cS45R1S160R4R3R2A3A3Fn;Frho1;Frho0;FP0;").
Proof.
  intros P0 rho0 rho1 n r r' t tr md md' Hag Hme (Ai & kc & HJ'). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0 [] [] (BXk K0) PA (KcG_ok _ _) ALA NF nd_Z Ai kc rho1 rho1 t tr md md' (Pos.le_refl _) (nd_Z_NF) (agree_below_refl _ _) Hme HJ').
Qed.

Lemma step_s0_dir : ltac2:(tb__ "0|0|
S3S3OF_;S3R2R1A1S122Vp3;R2A2F_;Fr;S2dS46Q40A1A1S70S45S6bS45S56VKcD;R4R3S92S76A5SdaR4R1A5VQ;A3Ftp;F_;FP0;Frho0;").
Proof.
  intros rho0 P0 HP0Z tp. pose proof K_T_pos as KT1.
  assert (HK0 : 0 <= K0) by (unfold K0, KU; lia).
  assert (HP0SH : forall r, P0 r -> SH0 r) by (intros r H; destruct (HP0Z r H) as (_ & [X _] & _); exact X).
  destruct s0_site as (Hn0 & HLV0 & HnL & HrunL & HerrV & Sp1 & Sp2 & Hn2 & Hset2 & Hs2 & Hcv & HC & HnC & Hs19).
  destruct (node_okb_sound _ _ Hn0) as (N1 & N2 & N3 & _). destruct (node_okb_sound _ _ HnL) as (L1 & L2 & L3 & _).
  destruct (node_okb_sound _ _ HnC) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct d_facts as (Dcc & DT & DnT & Drun & _ & DQ & DPosts).
  destruct (node_okb_sound _ _ DnT) as (T1 & T2 & T3 & _).
  pose proof run_S0 as R0. rewrite HLV0 in R0.
  eapply JR_run; [exact HK0 | exact R0 | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  eapply JR_run; [exact HK0 | exact HrunL | exact L2 | exact L1 | exact L3 |].
  intros L rho2 [<-|[]] Hag2. cbn [la_state].
  eapply (etriple_conseq (P := SPA segs (JR KcD rho0 P0 K0 nd_Z) C_s0 rho2 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { apply (SPA_errV _ rho2 E_s0 tp w HerrV) in HS. change (errV E_s0) with A0_s0 in HS.
    apply (SPA_split segs _ rho2 A0_s0 0 (SLit (-2256)) _ tp w Sp1) in HS. change (ax_setS A0_s0 (ax_S A1_s0)) with A1_s0 in HS.
    apply (SPA_split segs _ rho2 A1_s0 0 (SLit (-2336)) _ tp w Sp2) in HS. change (ax_setS A1_s0 (ax_S A2_s0)) with A2_s0 in HS.
    destruct (rdsZ_range rho2) as (CR1 & CR2 & CR3).
    apply (SPA_reslice segs _ rho2 A2_s0 (irds A2_s0) _ (O_rdsC (SLit CAP0) []) tp w Hn2 eq_refl eq_refl eq_refl eq_refl ltac:(rewrite Hset2; exact Hs2) CR1 CR2 CR3) in HS.
    rewrite Hset2 in HS. change (ax_setS A2_s0 (ax_S A3_s0)) with A3_s0 in HS.
    unfold carve_chk in Hcv. apply andb_prop in Hcv as [Hcv Cb]. apply andb_prop in Hcv as [Cw Cc]. apply sv_eqb_sound in Cb.
    rewrite <- HC. exact (carveR rho0 P0 K0 HP0SH KcD nd_Z A3_s0 rho2 tp w N_rd (ss_next (ax_S A3_s0)) HS Cw (Pos.leb_refl _) Cb Cc). }
  apply (pure_callJ_ex AInv CST XGL ALA NF rho0 P0 [] [] (BXk K0) PA KcD KcD C_s0 Pre_rd s_s0 R_s0 Posts_rd_d rho2 tp nd_Z
           (J0d P0 rho0 rho2) (J0d P0 rho0 rho2) Q (KcG_ok _ _)).
  - intros rho3 tp3. apply (read_dir_sum_ex (J0d P0 rho0 rho2) (J0d P0 rho0 rho2) (J0d_stable P0 rho0 rho2 NF) (J0d_stable P0 rho0 rho2 NF)).
    + intros r t tr md HJ. destruct (JR_Kc _ _ _ _ _ _ _ _ _ HJ) as (_ & Hfds & _). rewrite Hfds. exact HD3.
    + intros r t tr md HJ. exact HJ.
  - exact fr_s0.
  - exact Dcc.
  - exact M1.
  - exact M3.
  - exact M4.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros rhoL tr' md' HJ'. exact HJ'.
  - intros L rho' HinL Hag'. rewrite DPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S C_s0)) (import_postA s_s0 Pre_rd P_rd_d C_s0 R_s0)) with (T_after Pre_rd C_s0 s_s0 R_s0 P_rd_d). rewrite DT.
    eapply JR_run; [exact HK0 | exact Drun | exact T2 | exact T1 | exact T3 |].
    intros Lf rho5 [<-|[]] Hag5. cbn [la_state].
    eapply (etriple_conseq (P := fun w => exists rho6, SPA segs (JR KcD rho0 P0 K0 nd_Z) D_rde rho6 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
    { destruct (qz_cleanup KcD rho0 P0 K0 [] E_rde ZDa ZDb D_rde rho5 tp w (KcG_ok _ _) lit_cells_nil DQ HP0SH HS) as (rho6 & _ & HS6). exists rho6. exact HS6. }
    apply etriple_ex. intros rho6. apply (HTrderr rho0 P0). exact HP0Z.
Qed.

Theorem r_dir_ex : ltac2:(tb__ "0|1|
S3S2dS46Q40A1A1S70S45S6bS45S97VAInv;VCST;VXGL;S8aVKcD;R2S122Vp3;A1S2fS2eS0S0A2M0A1S2fS2eG0S0A2A1Sf8VPA;S124AcS123R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (etriple_conseq (P := SPA segs (JR KcD rho (DrvIfaceR.P0Z p3) K0 nd_Z) S0f rho tp)); [intros w HS; exact (r_entry_glue fdsD rho _ w tp HS) | intros w' Hw'; exact Hw' |].
  apply (step_s0_dir rho (DrvIfaceR.P0Z p3) (fun r H => H)).
Qed.
End RDir.

End RE.
End DrvRe.

