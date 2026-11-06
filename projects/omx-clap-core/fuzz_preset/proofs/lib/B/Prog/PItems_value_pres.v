(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the INTERFACE of segment VALUE of parse_items' image-B walk.
   The segment PI_O_VAL .. PI_O_GROW2 splits at its two block boundaries into three walk files, each
   proving one spec below from the next:
     PItems_value.v       PI_O_VAL (0x87cd8) .. PI_O_PVAL (0x87d94): the kid slot's checks, the checked memset;
                          proves PItems_pres.v pi_val_spec d N from pv_call_spec d N.
     PItems_value_call.v  PI_O_PVAL: the call of parse_value (the kit's tparse_value_specX at S d, the window-float call
                          rule YCbqGcallW.v aj_call_xWF_sp at window e + 144); proves pv_call_spec d N from
                          pv_aftv_spec d N.
     PItems_value_aftv.v  PI_O_AFTV (0x87d98) .. PI_O_GROW2 (0x87e18) and the closer test PI_O_CLS1
                          (0x87f38 .. 0x87f54): v->n++, the result test, skip_ws, the ',' test, in->p++, grow; proves
                          pv_aftv_spec d N from the neighbours' specs (pi_body_spec below N, pi_close2_spec,
                          pi_epi_spec).
   The pres follow PItems_pres.v's conventions: Context {fx} is the CURRENT float state, fx0 the entry one; acc is in
   READING order; the nesting d is a parameter of the spec; the ledger's most / own follow ran; the travelling facts
   of form (b) are PItems_posb.pi_posb S Sc tr0 and PItems_posb.pi_live over the prefix trace tr0,
   next to its rd_blocks_move. No numeral here is an ADDRESS: 56 and 8 are LENGTHs (the pj_value node, a slot word);
   2, 3 are DERIVED (fuel arithmetic). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YPsym YC4aP YImgTop YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
(* the walk's world relation wle' pa_segs RZ_cf (YA0nH; PItems_pres.v's segment specs) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Open Scope Z_scope.

(* the kid slot of member n: kids + 56 n (image B computes 56 n as (n << 6) - (n << 3)) *)
Definition pv_slot (kids : Z) (n : nat) : Z := kids + 56 * Z.of_nat n.

(* what pi_val_k does after the value (t, r): jrl's tail (PjGrammar.v:311-316), verbatim; so
   pi_val_k f D o n cap accr nm y1 = jbind (jrv prh_jr_strtod f D y1) (pv_kont f D o n cap accr nm) *)
Definition pv_kont (f D : nat) (o : bool) (n cap : nat) (accr : list (list Z * jv)) (nm : list Z)
  (tr : jv * list Z) : M (jv * list Z) :=
  let '(t, r) := tr in
  match skip r with
  | c :: r1 =>
      if c =? 44 then jrl prh_jr_strtod f D o (S n) cap ((nm, t) :: accr) r1
      else if c =? closer o then jret (mk o (rev ((nm, t) :: accr)), r1)
      else jrefuse
  | [] => jrefuse
  end.

(* the free-order twin of pv_kont: jfl's body after the value (PresetReqAt.v :287-291, verbatim), at af1 = af ++ the
   value's frees ++ the key's block *)
Definition pv_jfk (f D : nat) (o : bool) (n cap : nat) (af1 r : list Z) (ok : list bool) : list Z :=
  match skip r with
  | c :: r1 => if c =? 44 then PresetReqAt.jfl ReaderRes.jr_strtod f D o (S n) cap af1 r1 ok
               else af1 ++ PresetReqAt.arrz o cap
  | [] => af1 ++ PresetReqAt.arrz o cap
  end.

(* the whole call's run, the value read: the prefix (ok0, tr0) now includes the value's own run; on a refused
   value the whole run is decided (jbind passes the refusal on) *)
Definition pv_run_after (d : nat) (o : bool) (x0 : list Z) (ok0 : list bool) (tr0 : list ev)
  (f n cap : nat) (acc : list (list Z * jv)) (nm : list Z) (res : option (jv * list Z)) : Prop :=
  match res with
  | Some tr =>
      forall ok1 r t ok2, pv_kont f (Nat.succ d) o n cap (rev acc) nm tr ok1 = (r, t, ok2) ->
        jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2)
  | None => forall ok1, jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (None, tr0, ok1)
  end.

Section vp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* pi_val_pre's existential body, with its witnesses as parameters *)
Definition pv_vdata (regs0 : bvmap 5 word) (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (S : astate) (ly : alayout)
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs) (memc : word -> option byte) (N : nat)
  (f n cap : nat) (acc : list (list Z * jv)) (kids keys : Z) (Di : list (Z * Z)) (nm : list Z) (Dk : list (Z * Z))
  (pc : Z) (ok0 : list bool) (tr0 : list ev) (D0 : list (Z * Z)) (Lamc : list (Z * Z)) (peakc cntc failc ranc : Z)
  : Prop :=
    pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own /\
    (length (rest_atR tb text pc) <= N)%nat /\ (n < cap)%nat /\
    pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di /\
    Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
    pj_apartR (pi_sblk o kids keys cap) v /\
    pi_key (rdW Wc memc) (prh_lin Lamc) o keys n nm Dk /\
    Permutation D0 (pi_sblk o kids keys cap ++ Di ++ Dk) /\
    (2 * length (rest_atR tb text pc) + 1 <= f)%nat /\
    pi_val_eq d o (rest_atR tb text p) ok0 tr0 f n cap acc nm (rest_atR tb text pc) /\
    pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
    rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
    PItems_posb.pi_posb S Sc tr0 /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
    Ledger.lsum D0 = PjGrammar.held tr0 /\
    rd_room Sc (snd (fst (pi_val_k f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) []))) /\
  (* THE BATCH KIT'S INVARIANTS, verbatim from pi_val_pre *)
  pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap (Nat.succ n) /\ pi_ncaps (rdW Wc memc) kids acc /\
  exists af lk, pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af /\
    (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) Dk = lk) /\
    pi_fl_eqV d o (rest_atR tb text p) ok0 f n cap af lk (rest_atR tb text pc).

Lemma pv_val_pre_iff : forall fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW,
  pi_val_pre (fx := fx) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs N CTX0 CW <->
  (pi_fpok fx0 fx /\
   pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
   YAkMemnorm.memnorm segs memc /\
   pi_frame regs0 regs W mem Wc memc e q v /\
   pi_regs regs q v o /\ pi_regs_body regs Wc memc v /\ getr regs 21 = w64 (-1) /\
   exists (f n cap : nat) acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc,
     pv_vdata regs0 e q v o text len tb p d Lam peak cnt fail ran most own S ly lyc Sc Hpc Wc memc N
       f n cap acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc).
Proof. intros. unfold pi_val_pre, pv_vdata. reflexivity. Qed.

(* AT PI_O_PVAL (0x87d94, `jal parse_value`): pi_val_pre's data at the memory after the memset, a0 = q, a1 = the
   kid slot, and the slot zeroed (the memset's work) *)
Definition pv_call_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (N : nat)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  pi_regs regs q v o /\ pi_regs_body regs Wc memc v /\ getr regs 21 = w64 (-1) /\
  getr regs 10 = w64 q /\
  exists (f n cap : nat) acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc,
    pv_vdata regs0 e q v o text len tb p d Lam peak cnt fail ran most own S ly lyc Sc Hpc Wc memc N
      f n cap acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc /\
    getr regs 11 = w64 (pv_slot kids n) /\
    pj_zeroR segs (rdW Wc memc) (pv_slot kids n).

(* AT PI_O_AFTV (0x87d98), back from parse_value: a0 is its answer; the prefix (ok0, tr0, D0, the ledger) now
   includes the value's run; the container is as before the call (v->n not yet raised), the kid slot holds the
   value's tree (or a freeable partial tree), the cursor is after the value (or somewhere, refused) *)
Definition pv_aftv_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (N : nat)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  pi_regs regs q v o /\ pi_regs_body regs Wc memc v /\ getr regs 21 = w64 (-1) /\
  exists (f n cap : nat) acc kids keys Di nm Dk (res : option (jv * list Z)) Dv ok0 tr0 D0 Lamc peakc cntc failc ranc,
    getr regs 10 = w64 (match res with Some _ => 0 | None => -1 end) /\
    (* the container, as before the call *)
    (n < cap)%nat /\
    pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di /\
    Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
    pj_apartR (pi_sblk o kids keys cap) v /\
    pi_key (rdW Wc memc) (prh_lin Lamc) o keys n nm Dk /\
    Permutation D0 (pi_sblk o kids keys cap ++ Di ++ Dk ++ Dv) /\
    (* the run and the ledger, through the value *)
    pv_run_after d o (rest_atR tb text p) ok0 tr0 f n cap acc nm res /\
    (* The batch kit: the move priced over the WHOLE call's granted trace (a refused value is not a granted prefix); in the
       Some arm pi_grant gives pi_led back by PItems_ledk1.pik1_move_regt *)
    rd_ledger_move Lam peak cnt fail ran most ok0 (prhPi_gtrace d o (rest_atR tb text p)) tr0 D0 Lamc peakc cntc
      failc ranc /\
    rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
    (* the travelling position and live requests through the value (parse_value's post transfer composed on the
       block's own over the prefix, as PItems_posb.pi_posb_call / pi_live_call do) *)
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
       PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr0) ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr0))%nat H0 hist' Sc) /\
    (* the hull use: over tr0 when the value was read (its trace is its all-granted one; with the position above it
       is PItems_posb.pi_posb S Sc tr0), over the whole call's all-granted list when it was refused (the post's
       conjunct, PItems_posb.pi_posb_hull_call) *)
    PresetHullBudget.hull_used S Sc (PresetReqAt.rd_hevs
      (match res with Some _ => tr0 | None => prhPi_gtrace d o (rest_atR tb text p) end)) /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
    Ledger.lsum D0 = PjGrammar.held tr0 /\
    room_live_cf Sc /\
    (* where the text and the node are, at the return state *)
    range_addressable (aview segs (w_H Wc) memc) SHADOW_OFF q 24 /\
    src_rd Wc memc text tb /\ prhReader_home B lyc Sc Hpc Lamc text len /\
    prhReader_at B lyc Sc Lamc regs0 e v 56 /\ range_addressable (aview segs (w_H Wc) memc) SHADOW_OFF v 56 /\
    prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own /\
    (* the kid and the cursor *)
    match res with
    | Some (t, r) =>
        pj_nodeR segs (rdW Wc memc) (prh_lin Lamc) (pv_slot kids n) t Dv /\
        (PjTree.depth t <= PjGrammar.MAXD - Nat.succ d)%nat /\
        exists pc, pj_in_okR segs (rdW Wc memc) q text len pc (Z.of_nat d + 1) tb /\ rest_atR tb text pc = r /\
          cntc + 2 * Z.of_nat (length r) + 2 < 2 ^ 64 - 1 /\
          (Nat.succ (length r) <= N)%nat /\ (2 * length r + 3 <= f)%nat /\
          rd_room Sc (snd (fst (pv_kont f (Nat.succ d) o n cap (rev acc) nm (t, r) [])))
    | None =>
        pj_fdR segs (rdW Wc memc) (prh_lin Lamc) (PjGrammar.MAXD - Nat.succ d) (pv_slot kids n) Dv /\
        pj_in_afterR segs (rdW Wc memc) q text len (Z.of_nat d + 1) 33
    end /\
    (* THE BATCH KIT'S INVARIANTS (pv_vdata's, carried through the value; K1Value's text 01:5xZ): the capacities, the completed
       slots' free order, the key's block, and per outcome the kid's free order and the model *)
    cap = PresetReqAt.ncap (Nat.succ n) /\ pi_ncaps (rdW Wc memc) kids acc /\
    exists af lk fv, pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af /\
      (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) Dk = lk) /\
      match res with
      | Some (t, r) =>
          pi_grant ok0 tr0 /\ pj_ncapR segs (rdW Wc memc) (pv_slot kids n) t /\
          (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
             exists F, PRH_PjOrder.pj_foR segs (rdW Wc memc) (prh_lin Lamc) nn (pv_slot kids n) Dv F /\
               map (fun b => snd b + cf_head) F = fv) /\
          (forall ok1, prhPi_frees d o (rest_atR tb text p) (ok0 ++ ok1) =
             pv_jfk f (Nat.succ d) o n cap (af ++ fv ++ lk) r ok1)
      | None =>
          (* the post's OUTCOME clause at this state (the refused value's own outcome clause, composed on pi_posb) *)
          (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
             (H0 : list Z) (hist : list YG00.chunk),
             PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
             PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
             PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) ->
             (fail < cnt \/ cnt + Z.of_nat (calls (prhPi_gtrace d o (rest_atR tb text p))) <= fail) ->
             ranc = ran /\ fst (jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) []) = (None, tr0) /\
             exists hist', PresetRoomPos.iface_room_pos sm x os
               (i + length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))))%nat H0 hist' Sc) /\
          (* the post's INJECTED-READING clause at this state (tpiP_injected at ok0 / tr0: the prefix granted all, the
             refused value's own clause tpvP_injected at its window, or its OUTCOME when the chosen failure lies past it) *)
          (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
             (H0 : list Z) (hist : list YG00.chunk),
             PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
             PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_items ReaderRes.jr_strtod d o
               (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
             PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items ReaderRes.jr_strtod d o
               (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
             cnt <= fail < cnt + Z.of_nat (calls (prhPi_gtrace d o (rest_atR tb text p))) ->
             PRH_Base.prh_granted ok0 cnt fail (calls tr0)) /\
          (cf_head = PresetReqAt.HEAD -> forall nn, (PjGrammar.MAXD - Nat.succ d <= nn)%nat ->
             exists F, PRH_PjOrder.pj_foR segs (rdW Wc memc) (prh_lin Lamc) nn (pv_slot kids n) Dv F /\
               map (fun b => snd b + cf_head) F = fv) /\
          (forall ok1, prhPi_frees d o (rest_atR tb text p) (ok0 ++ ok1) = (af ++ fv ++ lk) ++ PresetReqAt.arrz o cap)
      end.

(* AT PV_O_SEP (0x87dbc), back from the skip_ws after a value that was read: v->n has been raised, so the container
   holds the new member (nm, t) as its last one; the cursor is past the white space (its rest is skip r); the run
   and the ledger are as after the value (skip_ws allocates nothing); the room is the rest of the member's run *)
Definition pv_sep_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (N : nat)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  pi_regs regs q v o /\ pi_regs_body regs Wc memc v /\ getr regs 21 = w64 (-1) /\
  exists (f n cap : nat) acc kids keys Di nm t r pc ok0 tr0 D0 Lamc peakc cntc failc ranc,
    (Nat.succ n <= cap)%nat /\
    pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys (Nat.succ n) cap (acc ++ [(nm, t)]) Di /\
    Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) (acc ++ [(nm, t)]) /\
    pj_apartR (pi_sblk o kids keys cap) v /\
    Permutation D0 (pi_sblk o kids keys cap ++ Di) /\
    pv_run_after d o (rest_atR tb text p) ok0 tr0 f n cap acc nm (Some (t, r)) /\
    pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
    rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
    PItems_posb.pi_posb S Sc tr0 /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
    Ledger.lsum D0 = PjGrammar.held tr0 /\
    room_live_cf Sc /\
    pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own /\
    rest_atR tb text pc = skip r /\
    (Nat.succ (length r) <= N)%nat /\ (2 * length r + 3 <= f)%nat /\
    rd_room Sc (snd (fst (pv_kont f (Nat.succ d) o n cap (rev acc) nm (t, r) []))) /\
    (* THE BATCH KIT'S INVARIANTS after v->n++ (the value read, so granted; K1Value's text 01:5xZ): the container at S n slots,
       its model the tail pv_jfk of jfl after the value (= pi_fl_eq at the next loop head after the comma) *)
    pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap (Nat.succ n) /\ pi_ncaps (rdW Wc memc) kids (acc ++ [(nm, t)]) /\
    exists af1, pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys (Nat.succ n) Di (acc ++ [(nm, t)]) af1 /\
      (forall ok1, prhPi_frees d o (rest_atR tb text p) (ok0 ++ ok1) = pv_jfk f (Nat.succ d) o n cap af1 r ok1).

End vp.

(* the block after the value's skip_ws: B 0x87dbc (a LENGTH offset from the entry, as the PI_O offsets of PItems_defs.v) *)
Definition PV_O_SEP : Z := 0x384.

(* ---- the two inner block specs, PItems_pres.v's form (current float state fxc a binder, d a parameter; the journal
   pi_ajR and the goal pi_goalR at the walk's relation wle' pa_segs RZ_cf, as PItems_pres.v's segment specs) ---- *)
Definition pv_call_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pv_call_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_PVAL Wc memc mdc regs CW.
Definition pv_aftv_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pv_aftv_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_AFTV Wc memc mdc regs CW.
Definition pv_sep_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pv_sep_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PV_O_SEP Wc memc mdc regs CW.
