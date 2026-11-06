(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 355 of its 391 lines of code are new or changed and 975 lines of the source are left out. *)
(* Segment R17 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x819a8, 0x819cc], 9
   instructions, cut Inv_B819a8 -> cut Inv_B819d0 (plan-asan-ubsan.md section 2, row R17; section 4, PP =
   reac_ports_parse 0x883d0). rule 24: no function proved (a slot segment).

   0x819a8 ld a1,272(s1) reloads the catalogue row m = [A + 272]; 0x819ac beq a0,a1 is taken because the
   catalogue_match result a0 is m (the entry cut), so the sink jump 0x819b0 is not reached. 0x819b4 li a0,-18 and
   0x819b8 bltu s4,a0 compare Phi_r with 2^64 - 18: the branch is taken (Phi_r + 50 <= 2^64), so the branch to the
   trap routine 0x819bc `j 82fa0` is not taken (plan T06). 0x819c0 addi s2,s4,18 (s2 = Phi_r + 18), 0x819c4
   mv a0,s2, 0x819c8 ld a1,120(s1) (the port words' address [A + 120] = fr + 2528) and 0x819cc jal reac_ports_parse,
   returning to 0x819d0. The range has no instrumented shadow check of its own.

   reac_ports_parse is taken on its lib/B contract (lib/B/Prog/reac_ports_parse_c.v), a Section Hypothesis, never
   on its code: it reads the 20 port bytes at Phi_r + 18 (X(0)[18 .. 38) = rt_pbs, RtmB.rb_pbs_F), checks that they
   and the 12 bytes at fr + 2528 are marked usable, and with a declared port block (RtmB.rb_rtm_decl) returns 0 and
   writes the counts 4 n_in, 4 n_out, 16 bt 7 at fr + 2528, + 2532, + 2536; it writes only those 12 bytes and its own
   16 stack bytes [sp - 16, sp). It needs no mem_inv.

   FRA moves across the write set [sp - 16, sp) + [fr + 2528, fr + 2540) by Tac_slot.sl_fr_cl (the frame body and
   the callee window), with the heap invariant from RHelp.rh_ah and the entry-anchored window joined from the
   callee's stack post; ENT by Tac_slot.ent_store; the model step by sl_fra_move / ent_mat; RBE by
   RHelp.rh_RBE_keep. Entry and exit are the official cuts Inv_B819a8_at / Inv_B819d0_at of lib/B/Prog/SlotInv.v.
   Both cuts carry s11 = 32, which reac_ports_parse keeps (r17_evt's getr R 27).  v1.9.0 against the patched
   image: the pcs move +0x64, the row is [A + 272] (patched [A + 288]), Phi_r + 18 is in s2 (patched s9), the
   32 in s11 (patched s2) and CUR's n - c in s9 (patched s8). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcLeaf RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

Lemma r17_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* 0x819b8 bltu s4,a0 with a0 = -18: taken when Phi_r < 2^64 - 18. *)
Lemma r17_ltu : forall phi, 0 <= phi -> phi + 50 <= 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 phi) (Z_to_bv 64 (-18)) = true.
Proof.
  intros phi H0 H1. unfold bv_ltu. rewrite (MState.unsigned_lit phi) by lia.
  change (bv_unsigned (Z_to_bv 64 (-18))) with 18446744073709551598.
  apply Z.ltb_lt. change (2 ^ 64) with 18446744073709551616 in H1. lia.
Qed.

(* ---- the run of [0x819a8, 0x819d0) with the reac_ports_parse contract (ports_ok true -> a0 = 0) ---- *)
Lemma r17_evt : reac_ports_parse_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi q mr lo : Z) (bs : list byte),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 mr -> s4v = Z_to_bv 64 phi ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= q -> q + 12 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 mr)) ->
    bytes_at rsegs m (A + 120) (le8 (Z_to_bv 64 q)) ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    q mod 4 = 0 -> wr_at rsegs m q 12 -> (q + 12 <= phi + 18 \/ phi + 18 + 20 <= q) ->
    (phi + 18 + 20 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= phi + 18) ->
    (q + 12 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= q) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 20 -> addressable m q 12 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - 16, bv_unsigned sp); (q, q + 12)] x) ->
    RcLeaf.ports_ok (phi + 18) q bs = true ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x819d0) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1v /\
         getr R 19 = s3 /\ getr R 20 = s4v /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 18 = Z_to_bv 64 (phi + 18) /\ getr R 10 = Z_to_bv 64 0 /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp); (q, q + 12)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' q (le4 (Z_to_bv 64 (4 * RcLeaf.n_in bs))) /\
         bytes_at rsegs m' (q + 4) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out bs))) /\
         bytes_at rsegs m' (q + 8) (le4 (Z_to_bv 64 (16 * RcLeaf.bt bs 7))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x819a8) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi q mr lo bs -> -> -> HA0 HAb Hphi0 Hphi50 Hq0 Hqb R272 R120 Hlen HB Hqmod HWR Hdisj Hsep1 Hsep2
    ST Hlo16 HAC HSW HAp HAq HOutside Hok.
  pose proof (rh_rdn m (A + 272) (le8 (Z_to_bv 64 mr)) 8 R272 ltac:(apply length_le8)) as RD272.
  pose proof (rh_rdn m (A + 120) (le8 (Z_to_bv 64 q)) 8 R120 ltac:(apply length_le8)) as RD120.
  step.                                         (* 819a8 ld a1,272(s1) : a1 := mr *)
  step. if_true_by (r17_eqb_refl (Z_to_bv 64 mr)).   (* 819ac beq a0,a1 : taken *)
  step.                                         (* 819b4 li a0,-18 *)
  step.                                         (* 819b8 bltu s4,a0 : taken, the trap 819bc not reached *)
  first [ if_true_by (r17_ltu phi Hphi0 Hphi50)
        | lazymatch goal with
          | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
              replace c with true;
                [ cbv iota
                | symmetry; unfold bv_ltu; rewrite !MState.unsigned_lit_wrap; apply Z.ltb_lt;
                  Z.div_mod_to_equations; lia ]
          end ].
  step.                                         (* 819c0 addi s2,s4,18 *)
  step.                                         (* 819c4 mv a0,s2 *)
  step.                                         (* 819c8 ld a1,120(s1) : a1 := q *)
  step.                                         (* 819cc jal reac_ports_parse *)
  eapply evt_cut.
  { eapply PP with (p := phi + 18) (q := q) (lo := lo) (bs := bs).
    - first [ reflexivity | f_equal; lia ].
    - reflexivity.
    - lia.
    - lia.
    - exact ST.
    - exact Hlo16.
    - intros _ _. split; [exact Hlen | exact HB].
    - intros _ _. split; [exact Hqmod|]. split; [exact HWR|]. split; [exact Hdisj|].
      split; [exact Hsep1 | exact Hsep2].
    - intros _ _. split; [exact HAC|]. split; [exact HSW|]. split; [exact HAp | exact HAq].
    - intros _ _. exact HOutside. }
  intros ms' PO. unfold reac_ports_parse_post in PO. rewrite Hok in PO.
  destruct PO as (t0' & t1' & t2' & t3' & t4' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' &
                  E & WM & _ & STc & HI & HO & H8 & MUc).
  subst ms'.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 16 (split; [first [ reflexivity | f_equal; lia ]|]).
  split; [exact MUc|]. split; [exact WM|]. split; [exact STc|].
  split; [exact HI|]. split; [exact HO | exact H8].
Qed.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* reac_ports_parse (0x882c0), taken on its lib/B contract. *)
Hypothesis PP : reac_ports_parse_contract.

Lemma seg_R17 : forall b : nat,
  Hat B APIf ra (Inv_B819d0_at B APIf ra) b -> Hat B APIf ra (Inv_B819a8_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hb6 & HHB & H22 & HOUR & HCUR & Hsp120 & HRBE & H21 & Hb0 & HRF & Ha0 & Hsp24 & Hsp16 & Hsp96 &
     HAQ & H27)).
  subst c. subst b. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hfrpl & HfrA & _ & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (rh_hb B APIf ra g fr phi (rnb g 0) regs mem md HFRA) as (Hphinz & Hphi4k & Hphistk & _ & _).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
  destruct HRT as (HAC0 & HSW0 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (W0 & W1 & _); split; [exact W0 | exact W1]).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HA4 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  rewrite Haspz in Hwlo, Hwstk, Hfrpl.
  assert (Hspb : 0 <= sp <= APPMEM_END) by (unfold APPMEM_END in *; lia).
  unfold AC.GT in HGTfr.
  assert (HspHM : HIGHMEM_BEG + 1040000 <= sp) by lia.
  assert (HspH : 6283264 <= sp - 16) by (unfold HIGHMEM_BEG in HspHM; lia).
  (* the turn's model facts *)
  pose proof HRF as (HRB0 & Hnz & H20 & HF).
  destruct (rb_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0) in Hnb, HLF.
  change (Z.of_nat 0) with 0 in HF, HLF.
  (* the 20 port bytes at Phi_r + 18 *)
  assert (HLS : bytes_at rsegs mem (phi + 18) (rt_pbs (g_in g))).
  { rewrite (rb_pbs_F (g_in g)).
    pose proof (rh_ba_sub mem phi (rt_F (g_in g) 0) 18 20 HF ltac:(rewrite HLF; lia)) as Hs.
    replace (phi + Z.of_nat 18) with (phi + 18) in Hs by lia. exact Hs. }
  pose proof (rb_pbs_len (g_in g)) as Hpbslen.
  assert (Hsz : AC.a_size (rnb g 0) = rnb g 0) by (unfold AC.a_size; lia).
  destruct HHB as (Hnz0 & HAphi0). pose proof HAphi0 as HAphi. rewrite Hsz in HAphi.
  assert (HAp : addressable mem (phi + 18) 20) by (apply (addressable_sub mem phi (rnb g 0) 18 20 HAphi); lia).
  pose proof HAphi as (Hphi0 & _ & HphiE & _).
  assert (Hphi50 : phi + 50 <= 2 ^ 64) by (unfold APPMEM_END in HphiE; lia).
  (* ports_ok: both pointers non-zero and the port block declared *)
  assert (Hok : RcLeaf.ports_ok (phi + 18) (fr + 2528) (rt_pbs (g_in g)) = true).
  { unfold RcLeaf.ports_ok. rewrite (rb_rtm_decl (g_in g)), !andb_true_r.
    apply andb_true_intro. split; apply negb_true_iff; apply Z.eqb_neq; lia. }
  assert (HWRq : wr_at rsegs mem (fr + 2528) 12).
  { split; [lia|]. split; [lia|]. intros i Hi. apply (Hfrwr (fr + 2528 + i)); lia. }
  pose proof (addressable_app mem (fr + 2528) 12 HAQ) as Happq.
  (* the block and the frame are disjoint *)
  pose proof (rh_blk_fr B APIf ra g fr phi (rnb g 0) regs mem md HFRA ltac:(lia)) as Hblkfr.
  assert (Hdisj : fr + 2528 + 12 <= phi + 18 \/ phi + 18 + 20 <= fr + 2528)
    by (destruct Hblkfr as [Hc|Hc]; [left; lia | right; lia]).
  assert (Hq4 : (fr + 2528) mod 4 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (Hsep1 : phi + 18 + 20 <= sp - 16 \/ sp <= phi + 18) by (left; lia).
  assert (Hsep2 : fr + 2528 + 12 <= sp - 16 \/ sp <= fr + 2528)
    by (destruct (Hfrpl 16 ltac:(lia)) as [Hc|Hc]; [left; lia | right; lia]).
  assert (HSTw : stk rsegs mem (g_S g - AF.SLOT_STACK) sp)
    by exact (proj1 (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia))).
  assert (HOutside : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x Hx. cbn [outside]. split; [|split; [|exact I]]; intro Hin.
    - destruct Hx as [HG|[HC|HSh]].
      + unfold GOT_CELL_K, HIGHMEM_BEG in *; lia.
      + unfold CELL_K, HIGHMEM_BEG in *; lia.
      + unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia.
    - destruct Hx as [HG|[HC|HSh]].
      + unfold GOT_CELL_K in *; lia.
      + unfold CELL_K in *; lia.
      + pose proof (Happq x ltac:(lia)) as Happx. exact (app_not_shadow x Happx HSh). }
  (* the two spills the segment reloads *)
  pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & _).
  pose proof (rh_spill_at regs mem A 272 (mrow (g_in g)) S272 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q272.
  pose proof (rh_spill_at regs mem A 120 (fr + 2528) Hsp120 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q120.
  (* the run *)
  eapply (sl_run_lib regs (Z_to_bv 64 0x819a8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x819d0 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27 /\
       getr R 18 = Z_to_bv 64 (phi + 18) /\ getr R 10 = Z_to_bv 64 0 /\
       munch [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (g_S g - AF.SLOT_STACK) sp /\
       bytes_at rsegs mem' (fr + 2528) (le4 (Z_to_bv 64 (4 * RcLeaf.n_in (rt_pbs (g_in g))))) /\
       bytes_at rsegs mem' (fr + 2528 + 4) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out (rt_pbs (g_in g))))) /\
       bytes_at rsegs mem' (fr + 2528 + 8) (le4 (Z_to_bv 64 (16 * RcLeaf.bt (rt_pbs (g_in g)) 7))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg, a0v in Ha0, H20, Hr9.
    eapply evt_mono.
    + apply (r17_evt PP) with (A := A) (phi := phi) (q := fr + 2528) (mr := mrow (g_in g))
        (lo := g_S g - AF.SLOT_STACK) (bs := rt_pbs (g_in g));
      try (match goal with
           | |- context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs)
           end);
      rewrite ?Haspz;
      [ exact Hr9 | exact Ha0 | exact H20 | lia | exact HA4 | exact Hphi0 | exact Hphi50 | lia | lia
      | exact Q272 | exact Q120 | exact Hpbslen | exact HLS | exact Hq4 | exact HWRq | exact Hdisj
      | exact Hsep1 | exact Hsep2 | exact HSTw | lia | exact HAC0 | exact HSW0 | exact HAp | exact HAQ
      | exact HOutside | exact Hok ].
    + intros ms' (R & m' & E & P2 & P3 & P4 & P8 & P9 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 &
                  P18 & P10 & MU & WM & ST' & HIq & HOq & H8q).
      exists R, (Z_to_bv 64 0x819d0), m'. split; [exact E|].
      split; [reflexivity|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P20|]. split; [exact P21|].
      split; [exact P22|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|].
      split; [exact P26|]. split; [exact P27|]. split; [exact P18|]. split; [exact P10|].
      match type of MU with
      | context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST'
      end.
      rewrite Haspz in MU, ST'.
      split; [exact MU|]. split; [exact WM|]. split; [exact ST'|].
      split; [exact HIq|]. split; [exact HOq | exact H8q].
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K18 & K10 &
       MU & WM & ST' & HIc & HOc & H8c) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (Fr18 : getr regs' 18 = Z_to_bv 64 (phi + 18)) by (rewrite Hreg; exact K18).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact K10).
    set (W := [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]).
    (* the write set and what lies outside it *)
    assert (HoutW : forall x, (x < sp - 16 \/ sp <= x) -> (x < fr + 2528 \/ fr + 2540 <= x) -> outside W x).
    { intros x H1 H2. unfold W. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (Hallapp : all_app W).
    { unfold W. cbn [all_app app_ivl]. split; [|split; [|exact I]].
      - intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
      - intros a Ha. exact (Happq a ltac:(lia)). }
    assert (HWin : forall x, ~ outside W x ->
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr + 24 <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx. unfold W in Hx. cbn [outside] in Hx.
      destruct (Z_le_gt_dec (sp - 16) x) as [H1|H1]; destruct (Z_lt_ge_dec x sp) as [H2|H2].
      - left. unfold APPMEM_END in *. lia.
      - right; left. lia.
      - right; left. lia.
      - right; left. lia. }
    assert (HPres : forall x, 0 <= x < 2 ^ 64 -> (exists bb, mbyte rsegs mem x = Some bb) ->
              exists bb, mbyte rsegs mem' x = Some bb).
    { intros x Hx Hb.
      destruct (rh_out_dec W x) as [Ho|Ho].
      - rewrite !rh_mbyte_mrd in Hb |- *. unfold mrd in *.
        rewrite (MU (wa x)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
      - unfold W in Ho. cbn [outside] in Ho. rewrite rh_mbyte_mrd.
        destruct (Z_lt_ge_dec x (fr + 2528)) as [Hl|Hl].
        + destruct ST' as (_ & _ & HST). destruct (HST x ltac:(unfold APPMEM_END in *; lia)) as (_ & bb & Hbb).
          exists bb. exact Hbb.
        + destruct (Z_lt_ge_dec x (fr + 2532)) as [Hl2|Hl2].
          * exact (rh_ba_rd mem' (fr + 2528) _ x HIc ltac:(rewrite length_le4; lia)).
          * destruct (Z_lt_ge_dec x (fr + 2536)) as [Hl3|Hl3].
            -- exact (rh_ba_rd mem' (fr + 2528 + 4) _ x HOc ltac:(rewrite length_le4; lia)).
            -- destruct (Z_lt_ge_dec x (fr + 2540)) as [Hl4|Hl4].
               ++ exact (rh_ba_rd mem' (fr + 2528 + 8) _ x H8c ltac:(rewrite length_le4; lia)).
               ++ destruct ST' as (_ & _ & HST).
                  destruct (HST x ltac:(unfold APPMEM_END in *; lia)) as (_ & bb & Hbb). exists bb. exact Hbb. }
    destruct (rh_ah B APIf ra g fr (hb1 phi (rnb g 0)) regs mem mem' md W HFRA MU WM HWin HPres)
      as (HAH' & HOWN' & HSTKeq & HSTKHeq).
    assert (HSTKfull : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (rh_stk_keep W mem mem' _ _ Hwin MU WM).
      intros x Hx _. pose proof Hwin as (_ & _ & HWw). destruct (HWw x Hx) as (_ & bb & Hbb).
      rewrite <- rh_mbyte_mrd in Hbb |- *.
      exact (HPres x ltac:(lia) (ex_intro _ bb Hbb)). }
    assert (HRO' : ro_agree rsegs mem').
    { apply (rh_ro_keep mem mem' W Hro MU). intros a Ha. pose proof (rh_ro_lt a Ha) as Hlt.
      unfold AC.GT in Hlt. apply HoutW; left; lia. }
    assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A)
      by (intros A' HA' HA'r; exact (rh_rg9_eq regs A A' Hr9 HA' HA64 HA'r)).
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs' mem mem' md W HFRA MU WM HRO'
               Hallapp).
      - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
          RT_AGLOB, RT_AGLOB_LEN.
        unfold W. cbn [disjoint_from]. repeat split; first [left; lia | exact I].
      - exact HAH'.
      - exact HSTKeq.
      - intros x Hx. apply HoutW; left; lia.
      - intros x Hx. apply HoutW; [destruct (Hfrpl 16 ltac:(lia)) as [Hc|Hc]; [left | right]; lia | left; lia].
      - intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply HoutW; right; lia.
      - intros x Hx. apply HoutW; right; lia.
      - intros x Hx. destruct (rh_sh_in B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA x Hx) as (Hsh' & _).
        unfold W. cbn [outside]. split; [|split; [|exact I]]; intro Hin.
        + apply (app_not_shadow x); [unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | exact Hsh'].
        + exact (app_not_shadow x (Happq x ltac:(lia)) Hsh').
      - intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply HoutW; right; lia.
      - eapply fsrec_stklo with (W := W); [exact HAH | exact MU |].
        intros x Hx1 Hx2. apply HoutW; lia.
      - intros x Hx.
        destruct (fra_in_apart B APIf ra g fr _ regs mem md HFRA x Hx) as (_ & Hxlo & Hxfr & _).
        apply HoutW; lia.
      - exact HSTKfull.
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs' mem' md')
      by exact (sl_fra_move B APIf ra g fr _ regs' regs' mem' md md' HFRAm
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g 0)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (rnb g 0)) regs mem mem' md W HENT HFRA MU);
        [ | exact HSTKeq | exact HSTKHeq | intros a _ Ho; exact (proj2 (HOWN' a) Ho) ].
      intros x Hx. destruct (rh_out_dec W x) as [Ho|Ho]; [left; exact Ho|].
      destruct (HWin x Ho) as [H|[H|H]]; [right; left; exact H | right; right; left; lia
                                        | right; right; right; exact H]. }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g 0)) mem' md')
      by exact (ent_mat APIf g (hb1 phi (rnb g 0)) mem' md md' HENT' Hmat).
    (* the facts the exit cut asks for *)
    assert (HoutA : forall x, A <= x < A + 448 -> outside W x)
      by (intros x Hx; apply HoutW; right; lia).
    assert (HoutPhi : forall x, phi <= x < phi + rnb g 0 -> outside W x).
    { intros x Hx. apply HoutW; [left; lia|]. destruct Hblkfr as [Hc|Hc]; [right | left]; lia. }
    assert (HoutFr : forall x, fr <= x < fr + 3136 -> (x < fr + 2528 \/ fr + 2540 <= x) -> outside W x).
    { intros x Hx Hx2. apply HoutW; [|exact Hx2].
      destruct (Hfrpl 16 ltac:(lia)) as [Hc|Hc]; [left | right]; lia. }
    assert (HHB' : HB mem' phi (rnb g 0)).
    { split; [exact Hnz0|]. exact (sl_addr_keep mem mem' W phi (AC.a_size (rnb g 0)) HAphi0 MU Hallapp). }
    assert (K : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Ho0 Ho1 Hs.
      exact (rh_spill_keep regs regs' mem mem' W A off v Hs Hr9 ltac:(lia) HA4 Ho0 Ho1 Fr9 MU
               (fun x Hx => HoutA x ltac:(lia))). }
    assert (HRBE' : RBE g fr regs' mem').
    { apply (rh_RBE_keep g fr regs regs' W mem mem' A HRBE MU Hallapp Hr9 ltac:(lia) HA4 Fr9 HoutA).
      intros x Hx. apply HoutW; left; unfold AC.GT, HIGHMEM_BEG in *; lia. }
    assert (HRF' : RFb g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs' mem').
    { apply (rh_RFb_keep3 g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs regs' W mem mem' MU
               (rb_RID_len (g_in g) 0) (rb_RFG_len (g_in g) 0 ltac:(lia)) ltac:(lia) HLF);
        [ intros x Hx; apply HoutFr; lia
        | intros x Hx; apply HoutFr; lia
        | intros x Hx; apply HoutFr; lia
        | exact HoutPhi | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr25 | exact HRF ]. }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. apply (rh_keep W mem mem' (fr + 2624) (OUR (g_in g)) MU); [|exact HOUR].
      rewrite OUR_length. intros x Hx. apply HoutFr; lia. }
    assert (HCUR' : CUR g 7 regs').
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite Fr23; exact Hc23 | rewrite Fr25; exact Hc25]. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB'|].
    split; [unfold rg in *; rewrite Fr22; exact H22|].
    split; [exact HOUR'|]. split; [exact HCUR'|].
    split; [apply K; [lia | lia | exact Hsp96]|].
    split; [exact HRBE'|].
    split; [unfold rg in *; rewrite Fr21; exact H21|].
    split; [reflexivity|].
    split; [exact HRF'|].
    split; [unfold rg; exact Fr18|].
    split; [unfold a0v, rg; exact Fr10|].
    split; [exact HIc|].
    split; [replace (fr + 2532) with (fr + 2528 + 4) by lia; exact HOc|].
    split; [apply K; [lia | lia | exact Hsp120]|].
    split; [apply K; [lia | lia | exact Hsp24]|].
    split; [apply K; [lia | lia | exact Hsp16]|].
    unfold rg; rewrite Fr27; exact H27.
Qed.

End S.
