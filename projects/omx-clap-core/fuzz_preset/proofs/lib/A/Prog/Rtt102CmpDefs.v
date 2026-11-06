(* fuzz_preset, program walk of round_trip_text ON THE #102 PINS, stretch CMP (lane RttCmp of WalkRtt102, the text owner):
   the IMAGE-GENERIC interfaces of the stretch's inner segments.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma support).
   THE CODE (A' +0x2e4 .. +0x328, A' capstone listing :187-203):
     +740 beqz s6, abort ; +744 mv a0, s6 ; +748 mv a1, s5 ; +752 jal __wrap_strcmp      (text, want)
     +756 bnez a0, abort ; +760 addi s7, s10, 0x20 ; +764 mv a0, s6 ; +768 jal __wrap_strlen (text)
     +772 mv a1, a0 ; +776 mv a0, s6 ; +780 mv a2, s7 ; +784 jal parse_noting               (text, len, &back)
     +788 mv s8, a0 ; +792 mv a0, s5 ; +796 jal __wrap_free                                 free (want)
     +800 mv a0, s6 ; +804 jal fuzz_free                                                     fuzz_free (text)
     +808 = RT_O2
   THE INNER CUTS: cmp_at_len at +772 (strlen returned: rtt_at_cmp's state, a0 = the text's length, s7 = back);
   cmp_at_pn at +788 (parse_noting returned: s8 not yet set, a0 = rc; the read-back's outcome cmp_out with the two
   blocks still to free, X, and the ledger entries still to drop, Y).
   ON THE BATCH KIT'S CUT 7cdbb61b5fa0 (GRANTED path only) this file states NO premise: parse_noting's own text gives the exact
   advance and, in its OUTCOME clause, the granted reading at the cut's position and prh_cons_from share (so its
   ran-out outcome is refuted at the call), the read-back tree's blocks over the reader's own list, its free order over
   pj_frees at every depth bound (at DOC_D a Theorem Labs lane's PresetFreeFo.pj_frees_wdoc_t turns it into fo t) and
   K0-CAP's pj_ncapR. The K0-POS-SWEEP, K0-POS-REFUSED, K0-TBLK and K0-FREEORD premises of earlier cuts are gone, and
   so are the composition's K0-UNIV-END (the cut's parse_noting text takes no cursor-end membership) and K0-SRC-CEIL
   (the cut's src_rd has no `+ 8`; the text block's own bound gives it, Rtt102CmpPNA.v cmp_pn).
   Numerals: none but the program points above (DERIVED: byte offsets inside round_trip_text). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetReqAtNoMiss PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnReader PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102Cut.
Import ListNotations.
Local Open Scope Z_scope.

(* the program points of the stretch (DERIVED: byte offsets inside round_trip_text, A' = B') *)
Definition RT_C1 : Z := 756.   (* strcmp's return: bnez a0 *)
Definition RT_C2 : Z := 772.   (* strlen's return: mv a1, a0 *)
Definition RT_C3 : Z := 788.   (* parse_noting's return: mv s8, a0 *)
Definition RT_C4 : Z := 800.   (* free (want)'s return: mv a0, s6 *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the model-run position the granted path reaches after parse_noting (the reader's events of the writer's text, every
   allocation granted) *)
Definition RT_K_P (D : rtt_in) : nat :=
  (RT_K_R D + length (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) []))%nat.

(* ---- +772: strlen has returned; the state is RT_CMP's, a0 = the text's length, s7 = back ---- *)
Definition cmp_at_len (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  (* fx BY NAME (the text owner's statement-trap rule, 2026-10-29): fxc is a second FPState in scope and class
     resolution would otherwise be free to pick it for rtt_at_cmp's class-implicit fx *)
  rtt_at_cmp (fx := fx) B ARx SK D fxc ly S Hp W regs mem md k pos /\
  getr regs 10 = w64 (Z.of_nat (length (ri_tb D))) /\
  getr regs 23 = w64 (frame_addr ly RT_CID pos + RT_BACK).

(* ---- the read-back's outcome, GRANTED ONLY (the cut 6e2b5d75a77 has no refusal arm: parse_noting's ran-out outcome is
   refuted at the call by the text's own OUTCOME clause from the call's position and its share of rtt_pre's
   prh_cons_from), with X the allocator blocks still to free (want's, the text's) and Y the ledger entries still to
   drop (the text's): rc = 0, the reading's calls exactly, its new blocks Db, back holds t over them; the block
   conjunct and the free-order list are the cut's RT_O2 forms verbatim, and so are rtt_rb's two last conjuncts at the
   the batch kit's cut (back's free order at every depth bound over the reader's own pj_frees, and K0-CAP's pj_ncapR), which only
   parse_noting's Some arm gives ---- *)
Definition cmp_out (D : rtt_in) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (pos : Z)
  (rc : Z) (Lamp : list (Z * Z)) (cntp ranp : Z) (X Y : list (Z * Z)) : Prop :=
  let t := ri_t D in let p := ri_p D in let back := frame_addr ly RT_CID pos + RT_BACK in
  let cnt0 := ri_cnt D + PjWriteHyp.wcalls t p in
  ranp = ri_ran D /\ rc = 0 /\ cntp = cnt0 + Z.of_nat (PjRoundTrip.tcalls t) /\
  exists Db, Permutation Lamp (Db ++ Y ++ ri_Lam D) /\
    (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B (ri_ly D) (ri_S D))) /\
    Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
    (cf_head = PresetReqAt.HEAD ->
       Permutation (map (fun b => snd b + cf_head) Db)
         (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
    (exists F, PRH_PjOrder.pj_foR segs (rdW W mem) (prh_lin Lamp) DOC_D back Db F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.fo t) /\
    Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
    Permutation (ablocks B ly S) (X ++ ablocks B (ri_ly D) (ri_S D) ++ ck_hblks Db) /\
    pj_nodeR segs (rdW W mem) (prh_lin Lamp) back t Db /\
    (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
       exists F, PRH_PjOrder.pj_foR segs (rdW W mem) (prh_lin Lamp) nn back Db F /\
         map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
    pj_ncapR segs (rdW W mem) back t.

(* ---- +788: parse_noting (text, len, &back) has returned, GRANTED; s6 = q, s5 = want, s7 = back, a0 = rc = 0. The
   model-run position is exact (RT_K_P, the text's outcome clause), the two buffers' capacities are the model's (the
   cut's), and the class-24 count is bounded (what the direct free's rl_b24_ok and fuzz_free's ccnt24 premise read) ---- *)
Definition cmp_at_pn (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  (* fx BY NAME, as above *)
  rtt_carry (fx := fx) B ARx SK D fxc ly S Hp W regs mem md k pos /\ rtt_back ly W mem pos /\ rtt_s11 regs /\
  rtt_copy_kept D W mem /\ getr regs 23 = w64 (frame_addr ly RT_CID pos + RT_BACK) /\
  exists q capw want cap rc Lamp peakp cntp ranp,
    getr regs 22 = w64 q /\ getr regs 21 = w64 want /\ getr regs 10 = w64 rc /\ q <> 0 /\ want <> 0 /\
    rtt_led B D ly S Hp W mem Lamp peakp cntp ranp 0 /\
    rtt_wblk B D ly S Hp want cap /\
    ~ In (q - cf_head, capw + cf_head) (ablocks B (ri_ly D) (ri_S D)) /\
    YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
    cmp_out D ly S W mem pos rc Lamp cntp ranp [(want, cap); (q - cf_head, capw + cf_head)] [(q, capw)] /\
    rtt_pos D S (RT_K_P D) /\
    cap = last (PresetReqAt.rcaps (ri_t D) (ri_p D)) 0 /\ capw = last (PresetReqAt.wcaps (ri_t D) (ri_p D)) 0.

End d.

(* ---- THE STATEMENT CHECK (the text owner's rule of 2026-10-29, in its AMENDED form: `Print` with implicits ON and
   notations OFF, so the Prop BODY is read, not only the type - `About` / `Check` cannot see a second FPState inside a
   body and the RTT layer reviewer measured a PASS that proved nothing). Both inner cuts bind a second FPState (fxc) beside the
   contract's fx; the premises below bind none of their own. PASS is `fx` in every class-implicit position of the
   cut's own predicates, and `fxc` only where this file passes it explicitly. ---- *)
Set Printing Implicit.
Unset Printing Notations.
Print cmp_at_len.
Print cmp_at_pn.
Print cmp_out.

Set Printing Notations.
Unset Printing Implicit.
