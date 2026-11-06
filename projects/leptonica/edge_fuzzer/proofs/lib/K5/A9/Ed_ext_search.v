(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_objkit LeptL_kit Ed_fp Ed_iface Ed_fpkit Numa_kit Ed_numa_leaf Ed_ext_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition search_post (gp s6 : word) (usp usp0 fr nas nad n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (found : bool) (i' : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (vl' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 usp0) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 usp0) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 fr) (Z_to_bv 64 nas) (Z_to_bv 64 nad) (Z_to_bv 64 n) s6 (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 32))
                  (Z_to_bv 64 i') (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + SHB)) t3' t4' t5' t6')
             F' (Z_to_bv 64 (if found then 0xee9a8 else 0xeea98)) (frm_clear fc') None m' (seg_rom asegs)
    /\ (if found then 1 <= i' < n else i' = n)
    /\ munch [(usp0 - 16, usp0); (fr + 48, fr + 48 + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp0
    /\ rw_cells asegs m' (fr + 48) [C4 vl'].

Lemma ext_search : forall (k : nat) (i : Z)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (usp usp0 fr lo nas cap arr nad : Z) (vals : list word) (live : list (Z * Z)) (sv vl : word),
  Z.of_nat k = Z.of_nat (length vals) - i -> 1 <= i < Z.of_nat (length vals) ->
  numa_obj live m nas cap arr vals -> acc asegs m nas 32 -> acc asegs m arr (4 * cap) ->
  rw_cells asegs m (fr + 32) [C4 sv] -> rw_cells asegs m (fr + 48) [C4 vl] -> acc asegs m (fr + 48) 4 ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  mem_inv asegs m -> stk asegs m lo usp0 ->
  lo + 16 <= usp0 -> usp0 <= 2^47 -> 0x10007fff8000 <= lo -> nas + 32 <= lo -> arr + 4 * cap <= lo -> fr + 64 <= lo ->
  (nas + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= nas) -> (nas + 32 <= 0x10000 \/ SEGTOP_A <= nas) ->
  (arr + 4 * cap <= 0x7fff7000 \/ 0x10007fff8000 <= arr) -> (arr + 4 * cap <= 0x10000 \/ SEGTOP_A <= arr) ->
  0 < fr -> fr mod 64 = 0 -> SEGTOP_A <= fr -> (fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  (fr + 64 <= nas \/ nas + 32 <= fr) -> (fr + 64 <= arr \/ arr + 4 * cap <= fr) ->
  (forall b kk a, In (b, kk) live -> b <= a < b + kk -> a < lo /\ (a < fr \/ fr + 64 <= a)) ->
  evt asegs (search_post gp s6 usp usp0 fr nas nad (Z.of_nat (length vals)) lo m)
    (MS (mkR ra (Z_to_bv 64 usp0) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 usp0) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 fr) (Z_to_bv 64 nas) (Z_to_bv 64 nad) (Z_to_bv 64 (Z.of_nat (length vals))) s6 (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 32))
              (Z_to_bv 64 i) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + SHB)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xee96c) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 F fc m usp usp0 fr lo nas cap arr nad vals live sv vl
    HK HI NOBJ ACCn ACCa CSV CVL ACCv G1 G2 MI ST LO UHI LOH NLO ALO FLO NSH NSEG ASH ASEG FR0 FR64 FRSEG FRSH FCD FCD0 LAP.
  { exfalso. lia. }
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  destruct (u32arr_nth vals i ltac:(lia)) as (wi & Hwi).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(usp0 - 16, usp0); (fr + 48, fr + 48 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  lwalk [e_numaGetFValue].
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (numaGetFValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm usp0 lo live nas cap arr vals i (fr + 48) wi vl) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJ
         | |- nth_error _ _ = _ => exact Hwi
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ mod _ = 0 => clear - FR64; Z.div_mod_to_equations; lia
         | |- _ => first [assumption | lia | unfold SEGTOP_A, SHB in *; lia]
         end. }
  intros ms' PO. destruct PO as (b1 & b2 & b3 & b4 & b5 & b6 & b7 & F2 & m1 & -> & MUl & WMl & MIl & STl & CVL1 & EF2).
  fix_ret_pc. subst F2.
  (* [comment removed for export] *)
  pose proof (agree_of_munch _ m m1 _ MUl (fun x Hx => Hx)) as AGl.
  assert (SVr : forall x, fr + 32 <= x < fr + 32 + 4 -> outside [(usp0 - 16, usp0); (fr + 48, fr + 48 + 4)] x) by (intros x Hx; cbn [outside]; clear - Hx FLO LO; lia).
  apply (rw_cells_agree_nw asegs m m1 _ _) in CSV; [| eapply agree_sub; [exact AGl|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply SVr; exact Hx].
  apply (ro_cells_agree asegs m m1 _ _) in G1; [| eapply agree_sub; [exact AGl|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; clear - Hx FLO LO LOH FRSEG; lia].
  apply (ro_cells_agree asegs m m1 _ _) in G2; [| eapply agree_sub; [exact AGl|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; clear - Hx FLO LO LOH FRSEG; lia].
  assert (SHr : forall y n x, 0 <= y -> 0 <= n -> y + n < 2^47 -> shad y <= x <= shad (y + n) -> outside [(usp0 - 16, usp0); (fr + 48, fr + 48 + 4)] x).
  { intros y n x Hy Hn Hy2 Hx. pose proof (shad_range y ltac:(lia)). pose proof (shad_range (y + n) ltac:(lia)). cbn [outside]. clear - Hx H H0 LOH LO FRSH FLO. lia. }
  apply (fun h => acc_agree m m1 _ nas 32 h AGl ltac:(lia) ltac:(intros x Hx; apply (SHr nas 32 x); lia)) in ACCn.
  apply (fun h => acc_agree m m1 _ arr (4 * cap) h AGl ltac:(lia) ltac:(intros x Hx; apply (SHr arr (4 * cap) x); lia)) in ACCa.
  apply (fun h => acc_agree m m1 _ (fr + 48) 4 h AGl ltac:(lia) ltac:(intros x Hx; apply (SHr (fr + 48) 4 x); lia)) in ACCv.
  apply (numa_obj_keep live m m1 nas cap arr vals) in NOBJ; [| apply (keeps_live_of_munch live _ m m1 MUl); intros b kk a Hin Ha; destruct (LAP b kk a Hin Ha) as [L1 L2]; cbn [outside]; clear - L1 L2 LO; lia].
  clear MI ST CVL SVr SHr AGl.
  (* [comment removed for export] *)
  step. step.
  lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F3 eqn:EF3 end.
  step.
  lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F4 eqn:EF4 end.
  step. step. fbr. all: try discriminate.
  all: lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0xee990) _ _ _ _) => step | _ => idtac end.
  all: lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F6 eqn:EF6 end.
  all: step; step; fbr; try discriminate.
  all: lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
  (* [comment removed for export] *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ ?FF (Z_to_bv 64 0xee9a8) (frm_clear ?fcx) _ _ _) =>
           apply evt_done; unfold search_post; exists true, i; do 16 eexists; exists FF, fcx, m1; eexists;
           split; [reflexivity|]; split; [lia|]; split; [exact MUl|]; split; [exact WMl|]; split; [exact MIl|]; split; [exact STl| exact CVL1]
       | _ => idtac end.
  (* [comment removed for export] *)
  all: step; step; rewrite (unsigned_lit i) by lia; rewrite swrap32_small by lia.
  all: destruct (Z.eq_dec (i + 1) (Z.of_nat (length vals))) as [EQ|NEQ]; [rewrite <- EQ; brF; rewrite EQ; step | brT].
  all: lazymatch goal with
       | |- evt _ _ (MS _ ?FF (Z_to_bv 64 0xeea98) (frm_clear ?fcx) _ _ _) =>
           apply evt_done; unfold search_post; exists false, (Z.of_nat (length vals)); do 16 eexists; exists FF, fcx, m1; eexists;
           split; [reflexivity|]; split; [lia|]; split; [exact MUl|]; split; [exact WMl|]; split; [exact MIl|]; split; [exact STl| exact CVL1]
       | _ => idtac end.
  all: eapply evt_cut; [eapply (IH (i + 1)) with (lo := lo) (cap := cap) (arr := arr) (vals := vals) (live := live); first [exact NOBJ | exact CVL1 | eassumption | lia] |].
  all: intros ms'' PO; destruct PO as (found & i' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15 & c16 & F' & fc' & m' & vl' & -> & HI' & MU' & WM' & MI' & ST' & CV');
     apply evt_done; unfold search_post; exists found, i'; do 16 eexists; exists F', fc', m', vl';
     split; [reflexivity|]; split; [exact HI'|]; split; [exact (munch_trans _ m m1 m' MUl MU')|]; split; [exact (wmono_trans asegs m m1 m' WMl WM')|];
     split; [exact MI'|]; split; [exact ST'| exact CV'].
Qed.
