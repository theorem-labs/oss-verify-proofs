(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSb8o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j AMTac ANodeA7 ANodeA6 ANodl61.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt34mx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt34mx ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalrrv ASecqib APopSC.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt34mx.ARt3_pop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt34mx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73.ARt3dl2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegD.
Context {Clg : Ceiling}.
  Variables (gp tp t0 t1 t2 a6 s6 t3 t4 t5 t6 : word) (a0g : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (s2v s10v s11v : word).   (* [comment removed for export] *)
  Variables (usp lo thr c maxc sb ri nf au mu mfa tsd ctx : Z) (scr scrM old : list byte) (junk : list word) (mm72 mm80 : word).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (thr + 208 + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (usp + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (sb + c * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size c).
  #[warnings="-notation-for-abbreviation"] Local Notation nc := ((mu - au) / class_size c).
  #[warnings="-notation-for-abbreviation"] Local Notation nm := (round_up (4 * (nf + (mu - au) / class_size c)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fe := (sb + c * 4294967296 + kFreeArrayOffset + mfa).
  Hypothesis PS : poison_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (uG + -64 + -48 + -128).   (* [comment removed for export] *)
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp - 1024.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis MXR : 2 <= maxc <= 16 /\ maxc = 2 * k.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis RIR : kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis SEP_tr : thr + 4096 <= ri \/ ri + 4096 <= thr.
  Hypothesis SEP_rs : ri + 4096 <= sb \/ sb + 2^37 <= ri.
  Hypothesis SEP_ts : thr + 4096 <= sb \/ sb + 2^37 <= thr.
  Hypothesis NF : 0 <= nf < k.
  Hypothesis AU : 0 <= au <= mu /\ mu mod kUserMap = 0 /\ au mod class_size c = 0 /\ au + (k - nf) * class_size c <= mu /\ mu - au < 9 * class_size c + kUserMap.
  Hypothesis CAP : mu <= 3750000000.   (* [comment removed for export] *)
  Hypothesis MFA : 0 <= mfa <= 469762048 (* [comment removed for export] *) /\ mfa mod kFreeArrayMapSize = 0 /\ mfa < 4 * (nf + nc).
  Hypothesis LJ : length junk = Z.to_nat nc.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis PCo : poison_consts m.
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis CCF144 : ro_cells rsegs m (CF + 144) [C8 (wz 0)].
  Hypothesis RNF : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis RMFA : rw_cells rsegs m (R + 24) [C8 (wz mfa)].
  Hypothesis RAU4 : rw_cells rsegs m (R + 32) [C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis REX : exists ex, rw_cells rsegs m (R + 68) [C1 ex].
  Hypothesis FRP : rw_cells rsegs m (uG + -64) (pop_frame (wz k) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0g (wz 0xb1d58) (wz R) (wz gfa_popret)).
  Hypothesis FRE : rw_cells rsegs m (uG + -64 + -48) (efas_frame scr (wz nc) (wz rb) (wz (nf + nc)) (wz R) (wz pop_efasret)).
  Hypothesis FRM : rw_cells rsegs m (uG + -64 + -48 + -128) (mapcb_frame scrM (wz (mu - au)) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)).   (* [comment removed for export] *)
  Hypothesis FAJ : u32arr rsegs m (free_array_of sb c + 4 * nf) junk.
  Hypothesis SHF : rw_cells rsegs m (sh fe) [CB (Z.to_nat ((nm - mfa) / 8)) old].
  Hypothesis TST : rw_cells rsegs m (thr + off_th_stats + 72) [C8 mm72; C8 mm80].

  Definition pop_sD_W : list (Z * Z) :=
    [(uG - 240, uG); (sh fe, sh fe + (nm - mfa) / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88); (R + 16, R + 32); (R + 32, R + 40); (R + 68, R + 69);
     (free_array_of sb c + 4 * nf, free_array_of sb c + 4 * nf + 4 * nc)].

  #[using="TST SHF FAJ FRM FRE FRP REX RAU4 RMFA RNF CCF144 TC PCo TSDL TPL LJ MFA CAP AU NF SEP_ts SEP_rs SEP_tr SBAL SBR RIR THR MXR CR SPH SPA LO ST MI TSS PS junk old scrM scr ctx tsd Clg"] Lemma pop_sD :
    evt rsegs (pop_grow_post gp tp a0g F fc m s10v s11v usp lo thr c maxc sb ri nf au mu nm pop_sD_W
                 (fun m' => bytes_at rsegs m' (sh fe) (repeat (Z_to_bv 8 250) (Z.to_nat ((nm - mfa) / 8)))
                            /\ rw_cells rsegs m' (thr + off_th_stats + 72) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + (nm - mfa)))]))
        (MS (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0 t1 t2 (wz (nm - mfa)) (wz 1) (wz fe) (wz (nm - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                 (wz fe) (wz efas_name) (wz PSC) (wz size) s6 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3 t4 t5 t6)
            F (wz mmap_after_pc) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CV. pose proof (class_size_range c CR) as CSR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof THR as [THRo THRc]. pose proof (aobj_facts _ _ THRo) as THF.
    unfold PSC, CF in *.
    assert (NCR : k - nf <= nc < 9 + 8192).
    { destruct AU as (A1 & A2 & A3 & A4 & A5). unfold kUserMap in A5. unfold kMaxSize in CSR.
      split; [apply Z.div_le_lower_bound; clear - A1 A4 CSR; lia| apply Z.div_lt_upper_bound; [clear - CSR; lia|]].
      clear - A5 CSR. nia. }
    assert (NM : 4 * (nf + nc) <= nm < 4 * (nf + nc) + 262144 /\ nm mod 262144 = 0) by (unfold kFaMap; apply roundup_famap_range; clear - NF NCR MXR; lia).
    eapply evt_cut; [eapply (map_post_ok gp tp t0 t1 t2 _ _ _ _ _ _ a6 _ _ _ _ _ s6 _ _ _ _ _ t3 t4 t5 t6 F fc m (uG + -64 + -48) lo (nm - mfa) fe fe scrM _ _ _ _ _ _
      (fun s => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         s = MS (mkR (wz efas_mapret) (wz (uG + -64 + -48)) gp tp t0' t1' t2' (wz nm) (wz fe) (wz fe) a1' a2' a3' a4' a5' a6' a7'
                     (wz (nm - mfa)) (wz R) (wz (mu - au)) (wz size) s6 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3' t4' t5' t6')
                F (wz efas_mapret) fc None m' (seg_rom rsegs)
         /\ munch [(uG + -64 + -48 - 128, uG + -64 + -48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (uG + -64 + -48)))|].
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF AU CAP NM NCR MFA; unfold kHighMemBeg, kFreeArrayOffset in *; first [lia | kcellz]).
    1: { unfold CF. destruct PCo as (_ & X & _). exact X. }
    1: { rewrite unsigned_lit by (clear - CV SBR CR MFA; unfold kHighMemBeg, kFreeArrayOffset in *; lia). clear - CV SBR CR MFA; unfold kHighMemBeg, kFreeArrayOffset in *; lia. }
    { intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m1 MU1 WM1 MI1 ST1. rewrite ?unsigned_lit in MU1, ST1 by (clear - CV LO LO0 SPH; lia).
      replace (ret_pc (wz efas_mapret)) with (wz efas_mapret : word) by (symmetry; apply ret_pc_even; [unfold efas_mapret; lia| reflexivity]).
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. exact (conj MU1 (conj WM1 (conj MI1 ST1))). }
    intros ms1 PO. destruct_exs PO. (first [ dand5 PO as -> MU1 WM1 MI1 ST1 | destruct PO as (-> & MU1 & WM1 & MI1 & ST1) ]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    destruct REX as [ex REX0]. xfer RNF MU1 WM1. xfer RMFA MU1 WM1. xfer RAU4 MU1 WM1. xfer REX0 MU1 WM1. xfer FRP MU1 WM1. xfer FRE MU1 WM1.
    unfold off_th_stats in *. xfer TST MU1 WM1. xfer CCF144 MU1 WM1.
    assert (FAJ1 : u32arr rsegs m1 (free_array_of sb c + 4 * nf) junk).
    { apply (u32arr_transport rsegs _ m m1 _ _ FAJ MU1 WM1). cbn [disjoint_from]. rewrite LJ. unfold free_array_of.
      split; [| exact I]. clear - CV LO SBR CR NF NCR MXR. unfold kHighMemBeg in *. lia. }
    assert (SHF1 : rw_cells rsegs m1 (sh fe) [CB (Z.to_nat ((nm - mfa) / 8)) old]).
    { eapply (rw_cells_transport rsegs _ m m1 _ _ SHF MU1 WM1). cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I]. left.
      unfold sh, kFreeArrayOffset. clear - CV LO SBR CR MFA NM NCR NF MXR. unfold kHighMemBeg, kShadowOffset in *. Z.div_mod_to_equations. lia. }
    assert (PCo1 : poison_consts m1).
    { destruct PCo as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13). unfold poison_consts.
      xfer P1 MU1 WM1. xfer P2 MU1 WM1. xfer P3 MU1 WM1. xfer P4 MU1 WM1. xfer P5 MU1 WM1. xfer P6 MU1 WM1. xfer P7 MU1 WM1.
      xfer P8 MU1 WM1. xfer P9 MU1 WM1. xfer P10 MU1 WM1. xfer P11 MU1 WM1. xfer P12 MU1 WM1. xfer P13 MU1 WM1.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    assert (TC1 : thread_cells m1 tp tsd ctx thr).
    { destruct TC as (T1 & T2 & T3 & T4 & T5 & Bnds). (first [ pose proof (Bnds) as dR_2; dand8 dR_2 as B1 B2 B3 B4 B5 B6 B7 B8 | pose proof Bnds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) ]). unfold thread_cells. rewrite TPL in *.
      xfer T1 MU1 WM1. xfer T2 MU1 WM1. xfer T3 MU1 WM1. xfer T4 MU1 WM1. xfer T5 MU1 WM1.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; clear - CV; lia. }
    pose proof TC as TC0. (first [ dand6 TC0 as _ _ _ _ _ Bnds | destruct TC0 as (_ & _ & _ & _ & _ & Bnds) ]). (first [ pose proof (Bnds) as dR_4; dand8 dR_4 as B1 B2 B3 B4 B5 B6 B7 B8 | pose proof Bnds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) ]). pose proof (aobj_facts _ _ B8) as CTF.
    eapply evt_cut; [eapply (efas_mapped_ok PS TSS gp tp x x0 x1 _ _ _ _ _ _ _ _ _ s6 _ _ _ _ _ x9 x10 x11 x12 F fc m1 (uG + -64) lo R nm mfa fe tsd ctx thr old scr mm72 mm80)|].
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF AU CAP NM NCR MFA TPL TSDL SEP_tr; unfold kHighMemBeg, kFreeArrayOffset, kShadowOffset, off_th_stats in *; first [lia | kcellz]).
    1: { destruct MFA as (_ & M2 & _). unfold kFreeArrayMapSize in M2. unfold kFreeArrayOffset.
         apply mod_add_lit; [lia| apply mod_add_lit; [lia| apply mod_add_lit; [lia| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact SBAL]| apply Znumtheory.Zdivide_mod; exists (c * 536870912); lia]| reflexivity]| apply (mod0_down _ 262144 8); [exists 32768; reflexivity| exact M2]]. }
    1: { clear - NM MFA. destruct NM as [N1 N2]. destruct MFA as (M1 & M2 & M3). unfold kFreeArrayMapSize in *. Z.div_mod_to_equations. lia. }
    1: { destruct NM as [_ N2]. destruct MFA as (_ & M2 & _). unfold kFreeArrayMapSize in M2.
         replace (nm - mfa) with (nm + (-1) * mfa) by lia. apply mod_add_lit; [lia| apply (mod0_down _ 262144 8); [exists 32768; reflexivity| exact N2]|].
         apply Znumtheory.Zdivide_mod. apply Z.divide_mul_r. apply (Z.divide_trans _ 262144); [exists 32768; reflexivity| apply Znumtheory.Zmod_divide; [lia| exact M2]]. }
    intros ms2 PO. destruct_exs PO. (first [ dand8 PO as -> MU2 WM2 MI2 ST2 RMFA2 SHF2 TST2 | destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & RMFA2 & SHF2 & TST2) ]). rewrite ?unsigned_lit in MU2, ST2 by (clear - CV LO LO0 SPH; lia).
    replace (ret_pc (wz pop_efasret)) with (wz pop_efasret : word) by (symmetry; apply ret_pc_even; [unfold pop_efasret; lia| reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    (* [comment removed for export] *)
    assert (SFB : 2147450880 <= sh fe /\ sh fe + (nm - mfa) / 8 <= 17594333495296 /\ 0 <= (nm - mfa) / 8).
    { unfold sh, kFreeArrayOffset. clear - CV SBR CR MFA NM NCR NF MXR. unfold kHighMemBeg, kShadowOffset in *. Z.div_mod_to_equations. lia. }
    unfold off_th_stats in MU2.
    apply (rw_cells_transport rsegs _ m1 m2 _ _ RNF) in MU2 as RNF2; [| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - CV LO RIR SBR THF SEP_tr SFB CR; unfold kHighMemBeg in *; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ RAU4) in MU2 as RAU2; [| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - CV LO RIR SBR THF SEP_tr SFB CR; unfold kHighMemBeg in *; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ REX0) in MU2 as REX2; [| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - CV LO RIR SBR THF SEP_tr SFB CR; unfold kHighMemBeg in *; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ FRP) in MU2 as FRP2; [| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - CV LO RIR SBR THF SEP_tr SFB CR; unfold kHighMemBeg in *; lia].
    apply (u32arr_transport rsegs _ m1 m2 _ _ FAJ1) in MU2 as FAJ2; [| exact WM2| cbn [disjoint_from]; rewrite LJ; unfold free_array_of; clear - CV LO RIR SBR THF SEP_tr SEP_rs SEP_ts SFB CR NF NCR MXR; unfold kHighMemBeg in *; lia].
    eapply evt_cut; [eapply (pop_carve_ok _ gp tp x13 x14 x15 _ _ _ _ _ _ _ s6 _ _ _ _ _ x23 x24 x25 x26 F fc m2 (uG) lo R sb c nf au (mu - au) 1 junk ex)|].
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF NCR MFA AU CAP; unfold kHighMemBeg, kUserMap in *; lia).
    1: (clear - SPA; Z.div_mod_to_equations; lia).
    1: { destruct AU as (_ & _ & AM & _). apply (mod0_down _ (class_size c) 16); [| exact AM]. apply (Z.divide_trans _ 32); [exists 2; reflexivity|]. apply Znumtheory.Zmod_divide; [clear - CSR; lia| exact (class_size_mod32 c CR)]. }
    1: (clear - SEP_rs CR; lia).
    1: (replace (au + (mu - au)) with mu by lia; exact RAU2).
    intros ms3 PO. destruct_exs PO. (first [ dand9 PO as -> MU3 WM3 MI3 ST3 RNF3 RAU3 REX3 FA3 | destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & RNF3 & RAU3 & REX3 & FA3) ]). rewrite ?unsigned_lit in MU3, ST3 by (clear - CV LO LO0 SPH; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    apply (rw_cells_transport rsegs _ m2 m3 _ _ RMFA2) in MU3 as RMFA3; [| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; unfold free_array_of; clear - CV LO RIR SBR SEP_rs CR NF NCR MXR; unfold kHighMemBeg in *; lia].
    unfold off_th_stats in TST2. apply (rw_cells_transport rsegs _ m2 m3 _ _ TST2) in MU3 as TST3; [| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; unfold free_array_of; clear - CV LO RIR SBR THF SEP_tr SEP_ts CR NF NCR MXR; unfold kHighMemBeg in *; lia].
    apply (bytes_at_transport rsegs _ m2 m3 _ _ SHF2) in MU3 as SHF3; [| cbn [disjoint_from]; rewrite repeat_length, Z2Nat.id by (clear - SFB; lia); unfold free_array_of; clear - CV LO RIR SBR SFB CR NF NCR MXR; unfold kHighMemBeg in *; lia].
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ ?r0 ?r1 ?r2 _ _ _ ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 _ _ _ _ _ _ _ _ _ _ ?u3 ?u4 ?u5 ?u6) _ _ _ _ ?mm _) =>
      apply evt_done; unfold pop_grow_post; exists r0, r1, r2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, mm end.
    split; [reflexivity|].
    split. { unfold pop_sD_W, off_th_stats. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
             unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact RNF3|]. split; [exact RMFA3|]. split; [replace mu with (au + (mu - au)) at 2 by lia; exact RAU3|]. split; [exact REX3|]. split; [exact FA3|].
    split; [exact SHF3| unfold off_th_stats; exact TST3].
  Qed.
End SegD.
