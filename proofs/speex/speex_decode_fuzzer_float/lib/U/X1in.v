(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fe X1m2 X1m3 X1m5 X1m6 X1ik X1ij X1im X1ip.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SITES.
Context {RCEIL : RunCeiling}.
Hypothesis HM : rmalloc_stmt.
Hypothesis HF : rfree_stmt.

#[using="HM"] Lemma malloc_siteG : forall {R} (k : option bptr -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (n SP RA SA lo B : Z) (errv : word) (fcs scs : list cell)
(gp tp : word) (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m ->
rauxv_ok m B -> SP <= B -> 0 <= SP < 2^64 ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - RMALLOC_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
0 <= n < 2^32 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
rw_cells rsegs m SP fcs -> rw_cells rsegs m SA scs -> SP <= SA ->
(forall (m' : mem) (s' : PState) (r : option bptr) (errv' : word) (y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
rauxv_ok m' B -> stk rsegs m' lo SP ->
rw_cells rsegs m' 316332 [C4 errv'] -> mem_inv rsegs m' ->
rheap_pres LB SP m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' SP fcs -> rw_cells rsegs m' SA scs ->
match r with
| None => va0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some p => exists Ab junk, va0 = Z_to_bv 64 Ab /\ rblock_range Ab n /\ RHEAP s' ((p, Ab, n) :: LB) m'
/\ rw_cells rsegs m' Ab [CB (Z.to_nat n) junk]
end ->
implM rsegs (k r) s' Q
(MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp y5 y6 y7 x8 x9 va0 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 RA) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (raw_malloc n) k) s Q
(MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 A_malloc) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP AUX SPB SP0 ST CEIL LO ERR MI TP Hn HRA HRA2 FR OS LE K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RMALLOC_STACK in LO.
eapply implM_bind.
{ unfold rmalloc_stmt, rmalloc_stmt_at in HM. unfold A_malloc.
eapply HM with (s := s) (LB := LB) (n := n) (lo := lo) (B := B) (errv := errv).
- exact HP.
- exact AUX.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RMALLOC_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity.
- exact Hn. }
cbv beta. intros r ps ms PO.
first [ sf_destruct 26%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ERR' AUX' HPR FA SO RES | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & RES) ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
rewrite (ret_pc_even RA) by assumption.
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
destruct r as [p|].
- first [ sf_destruct 7%nat RES as Ab junk Ha0 BR HP' BLK _ | sf_fb; destruct RES as (Ab & junk & Ha0 & BR & HP' & BLK & _) ]. exists Ab, junk. auto.
- exact RES.
Qed.

#[using="HF"] Lemma free_siteG : forall {R} (k : unit -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (p : bptr) (A n SP RA SA lo B : Z) (errv : word) (fcs scs : list cell)
(gp tp : word) (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> SP <= B -> 0 <= SP < 2^64 ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - RFREE_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
0 <= RA < 2^64 -> RA mod 2 = 0 ->
rw_cells rsegs m SP fcs -> rw_cells rsegs m SA scs -> SP <= SA ->
(forall (m' : mem) (s' : PState) (y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
rauxv_ok m' B -> stk rsegs m' lo SP ->
rw_cells rsegs m' 316332 [C4 errv] -> mem_inv rsegs m' ->
rheap_pres (lb_remove p LB) SP m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' SP fcs -> rw_cells rsegs m' SA scs ->
RHEAP s' (lb_remove p LB) m' ->
implM rsegs (k tt) s' Q
(MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp y5 y6 y7 x8 x9 va0 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 RA) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (raw_free p) k) s Q
(MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 A_free) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP HIN AUX SPB SP0 ST CEIL LO ERR MI TP HRA HRA2 FR OS LE K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RFREE_STACK in LO.
eapply implM_bind.
{ unfold rfree_stmt, rfree_stmt_at in HF. unfold A_free.
eapply HF with (s := s) (LB := LB) (p := p) (A := A) (n := n) (lo := lo) (B := B) (errv := errv).
- exact HP.
- exact HIN.
- exact AUX.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity. }
cbv beta. intros [] ps ms PO.
first [ sf_destruct 25%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MI' ST' ERR' AUX' HPR FA SO HP' | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & HP') ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
rewrite (ret_pc_even RA) by assumption.
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
Qed.
End SITES.

Definition sy_compact (sy : sync_st bptr) : sync_st bptr :=
if negb (sy_returned sy =? 0) then
mkSync (sy_data sy) (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy)))
(sy_storage sy) (sy_fill sy - sy_returned sy) 0 (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)
else sy.

Lemma compact_prefix : forall (buf : list Z) (bytes : list byte) (ret fill : nat),
firstn (length buf) (ubytes bytes) = buf -> (ret + fill <= length buf)%nat -> (length buf <= length bytes)%nat ->
firstn (length (firstn fill (skipn ret buf))) (ubytes (firstn fill (skipn ret bytes) ++ skipn fill bytes)) = firstn fill (skipn ret buf)
/\ (length (firstn fill (skipn ret buf)) <= length (firstn fill (skipn ret bytes) ++ skipn fill bytes))%nat.
Proof.
intros buf bytes ret fill Hpre Hrf Hlen.
assert (L1 : length (firstn fill (skipn ret buf)) = fill) by (rewrite firstn_length_le by (rewrite skipn_length; lia); reflexivity).
rewrite L1. split.
- rewrite ubytes_app, firstn_app, ubytes_firstn, ubytes_skipn, firstn_firstn, Nat.min_id.
rewrite firstn_length_le by (rewrite skipn_length, ubytes_length; lia). rewrite Nat.sub_diag, firstn_O, app_nil_r.
rewrite <- Hpre. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
- rewrite app_length, firstn_length_le by (rewrite skipn_length; lia). lia.
Qed.

Definition sync_buffer_rest (sy1 : sync_st bptr) (size : Z) : @X1qx.M PState (option (bptr * Z) * sync_st bptr) :=
if sy_storage sy1 - sy_fill sy1 <? size then
if INT_MAX - 4096 - sy_fill sy1 <? size then X1qx.mbind (ogg_sync_clear raw_free sy1) (fun sy' => X1qx.mret (None, sy'))
else
X1qx.mbind (match sy_data sy1 with
| Some p => raw_realloc p (size + sy_fill sy1 + 4096)
| None => raw_malloc (size + sy_fill sy1 + 4096)
end)
(fun ret => match ret with
| None => X1qx.mbind (ogg_sync_clear raw_free sy1) (fun sy' => X1qx.mret (None, sy'))
| Some q => X1qx.mret (Some (q, sy_fill sy1),
mkSync (Some q) (sy_buf sy1) (size + sy_fill sy1 + 4096) (sy_fill sy1) (sy_returned sy1)
(sy_unsynced sy1) (sy_headerbytes sy1) (sy_bodybytes sy1))
end)
else X1qx.mret (match sy_data sy1 with Some p => Some (p, sy_fill sy1) | None => None end, sy1).

Lemma ogg_sync_buffer_unfold : forall sy size,
ogg_sync_buffer raw_malloc raw_realloc raw_free sy size =
if sy_storage sy <? 0 then X1qx.mret (None, sy) else sync_buffer_rest (sy_compact sy) size.
Proof. intros. reflexivity. Qed.

Section BUFS.
Context {RCEIL : RunCeiling}.
Variable rhdr_known : PState -> bptr -> Prop.
Hypothesis rhdr_known_indep : forall s s' p, rhdr_known s p -> rhdr_known s' p.
Hypothesis HR : ogg_realloc_stmt rhdr_known.
Hypothesis HM : rmalloc_stmt.
Hypothesis HF : rfree_stmt.

Definition sync_buffer_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (sy : sync_st bptr) (size A D lo B : Z) (m : mem)
(r : option (bptr * Z) * sync_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (rv D' : Z) (bytes' : list byte) (LB' : list block),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' LB' m'
/\ cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32); (D, D + sy_storage sy)] (lb_remove_opt (sy_data sy) LB) (bv_unsigned sp) m m'
/\ sync_rep m' A D' (snd r) bytes' /\ sync_inv (snd r)
/\ rv = match fst r with None => 0 | Some (_, off) => D' + off end
/\ (forall q off, fst r = Some (q, off) -> sy_data (snd r) = Some q /\ off = sy_fill (snd r))
/\ ( (LB' = LB /\ D' = D /\ sy_data (snd r) = sy_data sy /\ sy_storage (snd r) = sy_storage sy)
\/ (exists q, sy_data (snd r) = Some q /\ LB' = (q, D', sy_storage (snd r)) :: lb_remove_opt (sy_data sy) LB
/\ rblock_range D' (sy_storage (snd r)) /\ (sy_data sy <> None -> rhdr_known s' q))
\/ (snd r = ogg_sync_init /\ D' = 0 /\ LB' = lb_remove_opt (sy_data sy) LB) ).

Ltac buf_clear_tail Esd HPx MU WM CMtac :=
let OSZ := fresh "OSZ" in
try (unfold implM; iprefix);
zstep; lstep; lstep; lstep; lstep;
zstep; zstep; zstep; zstep;
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned ?spv + -32) _, STx : stk rsegs _ _ _ |- _ => release_frame FRx STx (bv_unsigned spv) end;
zstep;
apply evt_done; cbv beta iota; try (apply impl_ret_ok; apply evt_done); cbn [fst snd];
lazymatch goal with OSx : rw_cells rsegs ?mx ?Av [C8 _; C8 _; C8 _; C8 _] |- _ => pose proof (sync_cells_zero mx Av OSx) as OSZ end;
unfold sync_buffer_post; cbn [fst snd]; rewrite Esd; sf_eexists 14%nat;
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end; eexists; first [ unshelve sf_eexists 3%nat; [ exact (0) | exact (0) | exact ((@nil byte)) | ] | sf_fb; exists 0, 0, (@nil byte) ];
lazymatch type of HPx with RHEAP _ ?LBx _ => exists LBx end;
split; [reflexivity|]; split; [assumption|]; split; [assumption|];
split; [ lazymatch goal with TP : _ = Z_to_bv 64 RATP |- _ => rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; lazymatch goal with E : rw_cells rsegs _ 316332 _ |- _ => exact E end end |];
split; [ lazymatch goal with AUX : rauxv_ok _ _ |- _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil end |];
split; [congruence|]; split; [congruence|];
split; [ eapply RHEAP_frame_proof; [exact HPx| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil |];
split; [ CMtac |];
split; [ split; [exact OSZ|]; split; [unfold sync_fields_ok, int31; cbn -[Z.lt Z.le Z.pow]; lia|]; split; [cbn; repeat split; reflexivity|]; cbn; lia |];
split; [unfold sync_inv, bytes_ok; cbn [sy_returned sy_fill sy_buf sy_headerbytes sy_bodybytes ogg_sync_init]; rewrite zlength_nil; repeat split; try lia; apply Forall_nil|];
split; [reflexivity|]; split; [intros q off Hq; discriminate Hq|];
right; right; split; [reflexivity|]; split; reflexivity.

#[using="HF"] Lemma buf_clear : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st st2 : PState) (LB : list block) (sy sy1 : sync_st bptr) (size A D lo B : Z) (m0 m2 : mem) (errv : word)
(j8 j24 : list byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
RHEAP st2 LB m2 -> rauxv_ok m2 B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 32 <= B ->
stk rsegs m2 lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - OGG_REALLOC_STACK ->
rw_cells rsegs m2 316332 [C4 errv] -> mem_inv rsegs m2 -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m2 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m2 A [C8 (Z_to_bv 64 D); CB 24 j24] ->
sy_data sy1 = sy_data sy ->
match sy_data sy with Some p => 0 < D /\ In (p, D, sy_storage sy) LB | None => D = 0 end ->
0 <= D -> D + sy_storage sy <= alloc_ceiling -> 0 <= sy_storage sy ->
ps_fa st2 = ps_fa st -> ps_so st2 = ps_so st ->
cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32); (D, D + sy_storage sy)] (lb_remove_opt (sy_data sy) LB) (bv_unsigned sp) m0 m2 ->
implM rsegs (X1qx.mbind (ogg_sync_clear raw_free sy1) (fun sy' => X1qx.mret (@None (bptr * Z), sy'))) st2
(sync_buffer_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB sy size A D lo B m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30584) fc None m2 (seg_rom rsegs)).
Proof.
intros until x31. intros HP AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS Edata HBLK D0 D1 ST0 FA SO CM.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL', D1. unfold OGG_REALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
unfold ogg_sync_clear. rewrite Edata.
unfold implM. iprefix.

zstep. zstep. if_cases CN; zify_cond CN; rewrite ?unsigned_lit in CN by lia.
all: rewrite ?land_ones64, ?Z.mod_small in CN by lia.
-
destruct (sy_data sy) as [p|] eqn:Esd; [exfalso; lia|].
apply evt_done. apply implM_retb. apply implM_ret.
buf_clear_tail Esd HP MU WM
ltac:(eapply cmod_trans; [exact CM|]; cbn [lb_remove_opt];
eapply (cmod_weaken _ _ LB _ (bv_unsigned sp) (bv_unsigned sp)); [eapply cmod_of_munch; [exact MU| exact WM]| lia| intros b Hb; exact Hb|];
intros x Hx; cbn in Hx |- *; lia).
-
destruct (sy_data sy) as [p|] eqn:Esd; [| exfalso; lia]. destruct HBLK as [_ HIN].
zstep. apply evt_done. apply implM_bind_assoc.
eapply (free_siteG HF _ _ st2 LB p D (sy_storage sy) (bv_unsigned sp + -32) 0x30590 A lo B errv _ _ gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- In _ _ => exact HIN
| |- RHEAP _ _ _ => exact HP
| |- rauxv_ok _ _ => exact AUX
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- _ mod 2 = 0 => reflexivity
| |- forall m', _ => idtac
| |- _ => try (unfold RFREE_STACK; lia)
end.
clear AUX ST ERR MI FR OS. rename MU into MU0. rename WM into WM0.
intros m3 st3 y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 AUX ST ERR MI HPR FA3 SO3 FR OS HP3.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 32)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
apply implM_retb. apply implM_ret.
buf_clear_tail Esd HP3 MU WM
ltac:(eapply cmod_trans; [exact CM|]; cbn [lb_remove_opt];
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR| lia| intros b Hb; exact Hb| intros x Hx; exact Hx]|];
eapply (cmod_weaken _ _ (lb_remove p LB) _ (bv_unsigned sp) (bv_unsigned sp)); [eapply cmod_of_munch; [exact MU| exact WM]| lia| intros b Hb; exact Hb|];
intros x Hx; cbn in Hx |- *; lia).
Qed.

#[using="Type"] Lemma buf_grow_done : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st st3 : PState) (LB : list block) (sy sy1 : sync_st bptr) (q : bptr) (size A D D' ns lo B : Z) (m0 m3 : mem) (errv : word)
(j8 : list byte) (bytes' : list byte) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
RHEAP st3 ((q, D', ns) :: lb_remove_opt (sy_data sy) LB) m3 -> rblock_range D' ns ->
rauxv_ok m3 B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 32 <= B ->
stk rsegs m3 lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - OGG_REALLOC_STACK ->
rw_cells rsegs m3 316332 [C4 errv] -> mem_inv rsegs m3 -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m3 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m3 A (sync_cells D sy1) ->
rw_cells rsegs m3 D' [CB (Z.to_nat ns) bytes'] ->
sync_fields_ok sy1 -> sync_inv sy1 -> sy_returned sy1 = 0 -> 0 <= ns < 2^31 -> sy_fill sy1 <= ns ->
firstn (length (sy_buf sy1)) (ubytes bytes') = sy_buf sy1 -> (length (sy_buf sy1) <= length bytes')%nat ->
(sy_data sy <> None -> rhdr_known st3 q) ->
ps_fa st3 = ps_fa st -> ps_so st3 = ps_so st ->
cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32); (D, D + sy_storage sy)] (lb_remove_opt (sy_data sy) LB) (bv_unsigned sp) m0 m3 ->
implM rsegs (X1qx.mret (Some (q, sy_fill sy1),
mkSync (Some q) (sy_buf sy1) ns (sy_fill sy1) (sy_returned sy1)
(sy_unsynced sy1) (sy_headerbytes sy1) (sy_bodybytes sy1))) st3
(sync_buffer_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB sy size A D lo B m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 ns) (Z_to_bv 64 D') x11 x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30554) fc None m3 (seg_rom rsegs)).
Proof.
intros until x31. intros HP BR AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS BLK FOK INV RET0 Hns Hfn PRE PREL HK FA SO CM.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold OGG_REALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as R1 R2 R3 R4 R5 | sf_fb; destruct sfP_ as (R1 & R2 & R3 & R4 & R5) ]. unfold alloc_ceiling in R4.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
first [ sf_destruct 6%nat FOK as F1 F2 F3 F4 F5 F6 | sf_fb; destruct FOK as (F1 & F2 & F3 & F4 & F5 & F6) ]. unfold int31 in F1, F2, F3, F4, F5, F6.
first [ sf_destruct 5%nat INV as I1 I2 I3 I4 I5 | sf_fb; destruct INV as (I1 & I2 & I3 & I4 & I5) ].
pose proof BLK as BLK0. destruct BLK0 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LENb _].
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 32)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
unfold sync_cells, wz in OS.
apply implM_ret.

zstep. rewrite (sx32_lit (sy_fill sy1)) by (unfold int31; lia).
lstep. lstep. zstep. zstep. zstep.
zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
apply evt_done. cbn [fst snd].
unfold sync_buffer_post. cbn [fst snd sy_data sy_fill sy_storage]. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists. first [ unshelve sf_eexists 3%nat; [ exact ((D' + sy_fill sy1)) | exact (D') | exact (bytes') | ] | sf_fb; exists (D' + sy_fill sy1), D', bytes' ].
exists ((q, D', ns) :: lb_remove_opt (sy_data sy) LB).
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split; [exact FA|]. split; [exact SO|].
split. { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split. { eapply cmod_trans; [exact CM|].
eapply (cmod_weaken _ _ (lb_remove_opt (sy_data sy) LB) _ (bv_unsigned sp) (bv_unsigned sp)); [eapply cmod_of_munch; [exact MU| exact WM]| lia| intros b Hb; exact Hb|].
intros x Hx. cbn in Hx |- *. lia. }
split. { split; [| split; [unfold sync_fields_ok, int31; cbn -[Z.lt Z.le Z.pow]; lia| split; [cbn -[Z.lt Z.le]| cbn; lia]]].
- lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end.
- split; [lia|]. split; [apply (u8arr_of_rw_cells rsegs _ _ _ _ BLK)|]. split; [lia|]. split; [exact PRE| exact PREL]. }
split. { unfold sync_inv. cbn -[Z.lt Z.le]. rewrite RET0 in I1. repeat split; try lia. exact I5. }
split; [reflexivity|]. split; [intros q' off Hq; injection Hq as <- <-; split; reflexivity|].
right; left. exists q. split; [reflexivity|]. split; [reflexivity|]. split; [exact BR| exact HK].
Qed.

#[using="Type"] Lemma prefix_app : forall (buf : list Z) (bytes junk : list byte),
firstn (length buf) (ubytes bytes) = buf -> (length buf <= length bytes)%nat ->
firstn (length buf) (ubytes (bytes ++ junk)) = buf /\ (length buf <= length (bytes ++ junk))%nat.
Proof.
intros buf bytes junk H Hl. rewrite ubytes_app, firstn_app, H, app_length.
rewrite ubytes_length. replace (length buf - length bytes)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. split; [reflexivity| lia].
Qed.

#[using="rhdr_known_indep HR HM HF"] Lemma buf_rest : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st st1 : PState) (LB : list block) (sy sy1 : sync_st bptr) (size A D lo B : Z) (m0 m1 : mem) (errv : word)
(j8 : list byte) (bytes1 : list byte) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
RHEAP st1 LB m1 -> rauxv_ok m1 B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 32 <= B ->
stk rsegs m1 lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - OGG_REALLOC_STACK ->
rw_cells rsegs m1 316332 [C4 errv] -> mem_inv rsegs m1 -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m1 A (sync_cells D sy1) ->
sync_fields_ok sy1 -> sync_inv sy1 -> sync_data m1 D sy1 bytes1 -> sy_returned sy1 = 0 ->
sy_data sy1 = sy_data sy -> sy_storage sy1 = sy_storage sy -> sy_fill sy1 = sy_fill sy - sy_returned sy ->
match sy_data sy with
| Some p => In (p, D, sy_storage sy) LB /\ (sy_storage sy - (sy_fill sy - sy_returned sy) < size -> rhdr_known st p)
| None => True end ->
0 <= size < 2^31 ->
(sy_storage sy - (sy_fill sy - sy_returned sy) < size -> size + (sy_fill sy - sy_returned sy) + 4096 < MMAP_THRESHOLD) ->
0 <= D -> D + sy_storage sy <= alloc_ceiling -> (D + sy_storage sy <= 65536 \/ 450560 <= D) ->
ps_fa st1 = ps_fa st -> ps_so st1 = ps_so st ->
cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32); (D, D + sy_storage sy)] (lb_remove_opt (sy_data sy) LB) (bv_unsigned sp) m0 m1 ->
implM rsegs (sync_buffer_rest sy1 size) st1
(sync_buffer_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB sy size A D lo B m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 (sy_storage sy)) x11 x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30518) fc None m1 (seg_rom rsegs)).
Proof.
intros until x31. intros HP AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS FOK INV DATA RET0 Edata Est Efill HBLK Hsz Hbound D0 D1 D2 FA SO CM.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL', D1. unfold OGG_REALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as F1 F2 F3 F4 F5 F6 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6) ]. unfold int31 in F1, F2, F3, F4, F5, F6.
pose proof INV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ].
assert (Hfs : sy_fill sy1 <= sy_storage sy1).
{ unfold sync_data in DATA. destruct (sy_data sy1); [first [ sf_destruct 5%nat DATA as _ _ L1 _ L2 | sf_fb; destruct DATA as (_ & _ & L1 & _ & L2) ]| first [ sf_destruct 4%nat DATA as _ _ E1 E2 | sf_fb; destruct DATA as (_ & _ & E1 & E2) ]; rewrite E1 in I2]; unfold zlength in *; [lia|]. cbn in I2. lia. }
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 32)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
unfold sync_cells, wz in OS.
unfold sync_buffer_rest. rewrite Est. unfold implM. iprefix.

zstep. rewrite (sx32_lit (sy_fill sy1)) by (unfold int31; lia).
zstep. rewrite (swrap32_small (sy_storage sy - sy_fill sy1)) by lia.
zstep. if_cases CN1; zify_cond CN1; rewrite ?zb_signed_small, ?unsigned_lit in CN1 by lia.
-
replace (sy_storage sy - sy_fill sy1 <? size) with false by (symmetry; apply Z.ltb_ge; lia).

zstep. zstep. zstep.
zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
apply evt_done. cbv beta iota. apply impl_ret_ok. apply evt_done. cbn [fst snd].
unfold sync_buffer_post. cbn [fst snd]. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists. first [ unshelve sf_eexists 4%nat; [ exact ((D + sy_fill sy1)) | exact (D) | exact (bytes1) | exact (LB) | ] | sf_fb; exists (D + sy_fill sy1), D, bytes1, LB ].
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split; [exact FA|]. split; [exact SO|].
split. { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split. { eapply cmod_trans; [exact CM|].
eapply (cmod_weaken _ _ (lb_remove_opt (sy_data sy) LB) _ (bv_unsigned sp) (bv_unsigned sp)); [eapply cmod_of_munch; [exact MU| exact WM]| lia| intros b Hb; exact Hb|].
intros x Hx. cbn in Hx |- *. lia. }
split. { split; [| split; [exact FOK| split; [| ]]].
- lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end.
- unfold sync_data in DATA |- *. destruct (sy_data sy1); [| exact DATA].
first [ sf_destruct 5%nat DATA as X1 X2 X3 X4 X5 | sf_fb; destruct DATA as (X1 & X2 & X3 & X4 & X5) ]. split; [exact X1|]. split; [| split; [exact X3| split; [exact X4| exact X5]]].
lazymatch goal with |- u8arr _ ?mx _ _ => eapply (u8arr_transport _ _ m1 mx); [exact X2| exact MU| exact WM|] end.
cbn. lia.
- pose proof DATA as DATA'. unfold sync_data in DATA'. destruct (sy_data sy1); [first [ sf_destruct 4%nat DATA' as _ _ X3 _ | sf_fb; destruct DATA' as (_ & _ & X3 & _) ]; lia| destruct DATA' as (-> & -> & _); cbn; lia]. }
split; [exact INV|].
split. { unfold sync_data in DATA. destruct (sy_data sy1); [reflexivity|]. first [ sf_destruct 4%nat DATA as -> _ _ X4 | sf_fb; destruct DATA as (-> & _ & _ & X4) ]. lia. }
split. { intros q off Hq. destruct (sy_data sy1); [| discriminate Hq]. injection Hq as <- <-. split; reflexivity. }
left. split; [reflexivity|]. split; [reflexivity|]. split; [exact Edata| exact Est].
-
replace (sy_storage sy - sy_fill sy1 <? size) with true by (symmetry; apply Z.ltb_lt; lia).
specialize (Hbound ltac:(lia)). unfold MMAP_THRESHOLD in Hbound.

zstep. zstep. zstep. zstep. if_cases CN2; zify_cond CN2; rewrite ?zb_signed_small, ?unsigned_lit in CN2 by lia.
{   exfalso. unfold INT_MAX in *. lia. }
replace (INT_MAX - 4096 - sy_fill sy1 <? size) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).

zstep. zstep. zstep. zstep.
replace (size + sy_fill sy1 + 4096) with (sy_fill sy1 + size + 4096) by lia.
set (ns := sy_fill sy1 + size + 4096) in *.
assert (Hns : sy_storage sy < ns /\ 0 <= ns < 2^31 /\ sy_fill sy1 <= ns /\ ns < MMAP_THRESHOLD /\ 1024 <= ns) by (subst ns; unfold MMAP_THRESHOLD, INT_MAX in *; lia).
zstep. if_cases CN3; zify_cond CN3; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN3 by lia.
+
pose proof DATA as DATA'. unfold sync_data in DATA'.
destruct (sy_data sy1) as [p|] eqn:Esd1; [destruct DATA' as (X1 & _); exfalso; lia|].
first [ sf_destruct 4%nat DATA' as _ Ebytes Ebuf Est0 | sf_fb; destruct DATA' as (_ & Ebytes & Ebuf & Est0) ].

zstep. zstep. apply evt_done.
eapply (malloc_siteG HM _ _ st1 LB ns (bv_unsigned sp + -32) 0x30580 A lo B errv _ _ gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- RHEAP _ _ _ => exact HP
| |- rauxv_ok _ _ => exact AUX
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- _ mod 2 = 0 => reflexivity
| |- forall m', _ => idtac
| |- _ => try (unfold RMALLOC_STACK; lia)
end.
clear AUX ST ERR MI FR OS. rename MU into MU0. rename WM into WM0.
intros m2 st2 r errv2 y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 AUX ST ERR MI HPR FA2 SO2 FR OS RES.
assert (CM2 : cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32); (D, D + sy_storage sy)] (lb_remove_opt (sy_data sy) LB) (bv_unsigned sp) m0 m2).
{ eapply cmod_trans; [exact CM|]. rewrite <- Edata. cbn [lb_remove_opt].
eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp)); [eapply cmod_of_rheap_pres; exact HPR| lia| intros b Hb; exact Hb| intros x Hx; exact Hx]. }
destruct r as [q|].
* first [ sf_destruct 6%nat RES as D' junk -> BRq HPq BLKq | sf_fb; destruct RES as (D' & junk & -> & BRq & HPq & BLKq) ].
pose proof BRq as sfP_; first [ sf_destruct 5%nat sfP_ as Q1 Q2 Q3 Q4 Q5 | sf_fb; destruct sfP_ as (Q1 & Q2 & Q3 & Q4 & Q5) ]. unfold alloc_ceiling in Q4.
unfold implM. iprefix.
zstep. if_cases CN4; zify_cond CN4; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN4 by lia; [| exfalso; lia].
apply evt_done.
eapply (buf_grow_done ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st2 LB sy sy1 q size A D D' ns lo B m0 m2 errv2 j8 junk);
try eassumption; try lia.
all: first [ rewrite <- Edata; cbn [lb_remove_opt]; exact HPq
| exact OS
| rewrite Ebuf; reflexivity
| rewrite Ebuf; cbn; lia
| intros X; exfalso; apply X; rewrite <- Edata; reflexivity
| congruence ].
* destruct RES as (-> & HP2).
unfold implM. iprefix.
zstep. if_cases CN4; zify_cond CN4; [exfalso; apply CN4; reflexivity|].
apply evt_done.
lazymatch goal with OSx : rw_cells rsegs ?mx A _ |- _ => destruct (sync_cells_raw mx A D sy1 OSx) as [j24 OSR] end.
eapply (buf_clear ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st2 LB sy sy1 size A D lo B m0 m2 _ j8 j24);
try eassumption; try lia.
all: first [ rewrite Esd1; exact Edata | rewrite <- Edata; cbn; lia | unfold alloc_ceiling; lia | congruence ].
+
pose proof DATA as DATA'. unfold sync_data in DATA'.
destruct (sy_data sy1) as [p|] eqn:Esd1; [| destruct DATA' as (X1 & _); exfalso; lia].
first [ sf_destruct 5%nat DATA' as X1 X2 X3 X4 X5 | sf_fb; destruct DATA' as (X1 & X2 & X3 & X4 & X5) ].
rewrite <- Edata in HBLK. destruct HBLK as [HIN HK]. specialize (HK ltac:(lia)).
pose proof (rw_cells_of_u8arr rsegs _ _ _ X2) as BLK. replace (length bytes1) with (Z.to_nat (sy_storage sy)) in BLK by lia.

zstep. zstep. apply evt_done.
eapply (realloc_site rhdr_known HR _ _ st1 LB p D (sy_storage sy) ns (bv_unsigned sp + -32) 0x30550 A lo B errv bytes1 _ _ gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact BLK | exact OS | exact FR | exact ERR]
| |- In _ _ => exact HIN
| |- rhdr_known _ _ => eapply rhdr_known_indep; exact HK
| |- RHEAP _ _ _ => exact HP
| |- rauxv_ok _ _ => exact AUX
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- _ mod 2 = 0 => reflexivity
| |- forall m', _ => idtac
| |- _ => try (unfold OGG_REALLOC_STACK, MMAP_THRESHOLD in *; lia)
end.
clear AUX ST ERR MI FR OS BLK. rename MU into MU0. rename WM into WM0.
intros m2 st2 r errv2 y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 AUX ST ERR MI HPR FA2 SO2 FR OS RES.
assert (CM2 : cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32); (D, D + sy_storage sy)] (lb_remove_opt (sy_data sy) LB) (bv_unsigned sp) m0 m2).
{ eapply cmod_trans; [exact CM|]. rewrite <- Edata. cbn [lb_remove_opt].
eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp)); [eapply cmod_of_rheap_pres; exact HPR| lia| intros b Hb; exact Hb| intros x Hx; exact Hx]. }
destruct r as [q|].
* first [ sf_destruct 8%nat RES as D' junk -> BRq HPq BLKq HKq SAME | sf_fb; destruct RES as (D' & junk & -> & BRq & HPq & BLKq & HKq & SAME) ].
pose proof BRq as sfP_; first [ sf_destruct 5%nat sfP_ as Q1 Q2 Q3 Q4 Q5 | sf_fb; destruct sfP_ as (Q1 & Q2 & Q3 & Q4 & Q5) ]. unfold alloc_ceiling in Q4.
rewrite Z.min_r in BLKq by lia. replace (Z.to_nat (sy_storage sy)) with (length bytes1) in BLKq by lia. rewrite firstn_all in BLKq.
destruct (prefix_app _ _ junk X4 X5) as [PRE PREL].
unfold implM. iprefix.
zstep. if_cases CN4; zify_cond CN4; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN4 by lia; [exfalso; lia|].
apply evt_done.
eapply (buf_grow_done ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st2 LB sy sy1 q size A D D' ns lo B m0 m2 errv2 j8 (bytes1 ++ junk));
try eassumption; try lia.
all: first [ rewrite <- Edata; cbn [lb_remove_opt]; exact HPq
| exact OS
| intros _; exact HKq
| congruence ].
* first [ sf_destruct 4%nat RES as -> HP2 BLK2 HK2 | sf_fb; destruct RES as (-> & HP2 & BLK2 & HK2) ].
unfold implM. iprefix.
zstep. if_cases CN4; zify_cond CN4; [| exfalso; apply CN4; reflexivity].
apply evt_done.
lazymatch goal with OSx : rw_cells rsegs ?mx A _ |- _ => destruct (sync_cells_raw mx A D sy1 OSx) as [j24 OSR] end.
eapply (buf_clear ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st2 LB sy sy1 size A D lo B m0 m2 _ j8 j24);
try eassumption; try lia.
all: first [ rewrite Esd1; exact Edata | rewrite <- Edata; cbn; split; [lia| exact HIN] | unfold alloc_ceiling; lia | congruence ].
Qed.

#[using="Type"] Lemma compact_inv : forall sy : sync_st bptr, sync_inv sy -> sync_fields_ok sy ->
let sy1 := mkSync (sy_data sy) (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy)))
(sy_storage sy) (sy_fill sy - sy_returned sy) 0 (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy) in
sync_inv sy1 /\ sync_fields_ok sy1 /\ length (sy_buf sy1) = Z.to_nat (sy_fill sy - sy_returned sy)
/\ sy_buf sy1 = firstn (Z.to_nat (sy_fill sy - sy_returned sy)) (skipn (Z.to_nat (sy_returned sy)) (sy_buf sy)).
Proof.
intros sy sfH_; first [ sf_destruct 5%nat sfH_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfH_ as (I1 & I2 & I3 & I4 & I5) ]; intros sfH2_; first [ sf_destruct 6%nat sfH2_ as F1 F2 F3 F4 F5 F6 | sf_fb; destruct sfH2_ as (F1 & F2 & F3 & F4 & F5 & F6) ]. unfold int31 in *. unfold zlength in I2. cbn -[Z.sub Z.le Z.lt Z.of_nat Z.to_nat].
assert (L : length (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy))) = Z.to_nat (sy_fill sy - sy_returned sy)).
{ unfold ztake, zdrop. rewrite firstn_length_le by (rewrite skipn_length; lia). reflexivity. }
split; [| split; [unfold sync_fields_ok, int31; cbn -[Z.le Z.lt Z.sub Z.pow]; lia| split; [exact L| reflexivity]]].
unfold sync_inv. cbn -[Z.sub Z.le Z.lt Z.of_nat Z.to_nat ztake zdrop]. unfold zlength. rewrite L.
repeat split; try lia. apply bytes_ok_ztake, bytes_ok_zdrop, I5.
Qed.

#[using="rhdr_known_indep HR HM HF"] Lemma ogg_sync_buffer_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(st : PState) (LB : list block) (sy : sync_st bptr) (size A D lo B : Z) (bytes : list byte) (errv : word),
RHEAP st LB m -> sync_rep m A D sy bytes -> sync_inv sy ->
match sy_data sy with
| Some p => In (p, D, sy_storage sy) LB /\ (sy_storage sy - (sy_fill sy - sy_returned sy) < size -> rhdr_known st p)
| None => True end ->
0 <= size < 2^31 ->
(sy_storage sy - (sy_fill sy - sy_returned sy) < size -> size + (sy_fill sy - sy_returned sy) + 4096 < MMAP_THRESHOLD) ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 32 <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - OGG_REALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 size ->
implM rsegs (ogg_sync_buffer raw_malloc raw_realloc raw_free sy size) st
(sync_buffer_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB sy size A D lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HP REP INV HBLK Hsz Hbound AUX SPB SPA AB ST CEIL LO ERR MI TP -> ->.
unfold A_ogg_sync_buffer. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold OGG_REALLOC_STACK in LO.
first [ sf_destruct 4%nat REP as OS FOK DATA SEPA | sf_fb; destruct REP as (OS & FOK & DATA & SEPA) ]. unfold sync_cells, wz in OS.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as F1 F2 F3 F4 F5 F6 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6) ]. unfold int31 in F1, F2, F3, F4, F5, F6.
pose proof INV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ].
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
assert (DB : 0 <= D /\ D + sy_storage sy <= alloc_ceiling /\ (D + sy_storage sy <= 65536 \/ 450560 <= D)).
{ unfold sync_data in DATA. destruct (sy_data sy) as [p|].
- destruct HBLK as [HIN _]. pose proof (RHEAP_block_range_proof _ _ _ _ HP HIN) as sfP_; first [ sf_destruct 5%nat sfP_ as B1 B2 B3 B4 B5 | sf_fb; destruct sfP_ as (B1 & B2 & B3 & B4 & B5) ]. cbn [blk_addr blk_size fst snd] in *. lia.
- unfold alloc_ceiling. lia. }
pose proof DB as (DB0 & DB1 & DB2). unfold alloc_ceiling in DB1.
assert (Hfs : sy_fill sy <= sy_storage sy /\ (length (sy_buf sy) <= length bytes)%nat /\ Z.of_nat (length bytes) = sy_storage sy).
{ unfold sync_data in DATA. unfold zlength in I2. destruct (sy_data sy); [first [ sf_destruct 5%nat DATA as _ _ L1 _ L2 | sf_fb; destruct DATA as (_ & _ & L1 & _ & L2) ]; lia|].
first [ sf_destruct 4%nat DATA as _ -> E2 E3 | sf_fb; destruct DATA as (_ & -> & E2 & E3) ]. rewrite E2 in I2 |- *. cbn in I2 |- *. lia. }
destruct Hfs as (Hfs & Hbl & Hlen).
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
rewrite ogg_sync_buffer_unfold. unfold implM. iprefix.
carve_frame 32%nat ST.

zstep. zstep. zstep. zstep. zstep. zstep.
rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia).
zstep. if_cases CN0; zify_cond CN0; rewrite ?unsigned_lit in CN0 by lia; [exfalso; lia|].
replace (sy_storage sy <? 0) with false by (symmetry; apply Z.ltb_ge; lia).

zstep. zstep. rewrite (sx32_lit (sy_returned sy)) by (unfold int31; lia).
zstep. if_cases CN1; zify_cond CN1; rewrite ?unsigned_lit in CN1 by lia.
-
unfold sy_compact. replace (negb (sy_returned sy =? 0)) with false by (rewrite CN1; reflexivity).
apply evt_done.
eapply (buf_rest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st LB sy sy size A D lo B m _ errv _ bytes);
try eassumption; try reflexivity; try lia.
all: first [ eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| lazymatch goal with |- rw_cells _ _ _ (sync_cells _ _) => rewrite <- CN1; exact OS end
| lazymatch goal with |- sync_data ?mx _ _ _ =>
unfold sync_data in DATA |- *; destruct (sy_data sy); [| exact DATA];
first [ sf_destruct 5%nat DATA as X1 X2 X3 X4 X5 | sf_fb; destruct DATA as (X1 & X2 & X3 & X4 & X5) ]; split; [exact X1|]; split; [| split; [exact X3| split; [exact X4| exact X5]]];
eapply (u8arr_transport _ _ m mx); [exact X2| exact MU| exact WM| cbn; lia] end
| unfold alloc_ceiling; lia
| eapply (cmod_weaken _ _ (lb_remove_opt (sy_data sy) LB) _ (bv_unsigned sp) (bv_unsigned sp)); [eapply cmod_of_munch; [exact MU| exact WM]| lia| intros b Hb; exact Hb|];
intros x Hx; cbn in Hx |- *; lia ].
-
unfold sy_compact. replace (negb (sy_returned sy =? 0)) with true by (symmetry; apply (proj2 (negb_true_iff _)); apply Z.eqb_neq; exact CN1).
pose proof (compact_inv sy INV FOK) as sfP_; first [ sf_destruct 4%nat sfP_ as INV1 FOK1 LEN1 BUF1 | sf_fb; destruct sfP_ as (INV1 & FOK1 & LEN1 & BUF1) ]. cbv zeta in INV1, FOK1, LEN1, BUF1.
set (sy1 := mkSync _ _ _ _ _ _ _ _) in INV1, FOK1, LEN1, BUF1 |- *.

pose proof DATA as DATA'. unfold sync_data in DATA'.
destruct (sy_data sy) as [p|] eqn:Esd; [| first [ sf_destruct 4%nat DATA' as _ _ Ebuf Est0 | sf_fb; destruct DATA' as (_ & _ & Ebuf & Est0) ]; lia].
first [ sf_destruct 5%nat DATA' as X1 ARR0 X3 X4 X5 | sf_fb; destruct DATA' as (X1 & ARR0 & X3 & X4 & X5) ]. destruct HBLK as [HIN HK].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (u8arr_transport rsegs _ m mx D bytes ARR0 MU WM ltac:(cbn; lia)) as ARR end. clear ARR0.

zstep. rewrite (sx32_lit (sy_fill sy)) by (unfold int31; lia).
zstep. rewrite (swrap32_small (sy_fill sy - sy_returned sy)) by lia.
lstep.
zstep. if_cases CN2; zify_cond CN2.
+
assert (E0 : sy_fill sy - sy_returned sy = 0) by (destruct (Z.ltb_spec 0 (sy_fill sy - sy_returned sy)); destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) 9223372036854775808); cbn in CN2; try discriminate; lia).
lstep.
apply evt_done.
eapply (buf_rest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st LB sy sy1 size A D lo B m _ errv _ bytes);
try eassumption; try reflexivity; try lia.
1:{ eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil. }
1:{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil. }
1:{ unfold sync_data; subst sy1; cbn -[Z.lt Z.of_nat ubytes]; rewrite ?Esd.
split; [exact X1|]. split; [exact ARR|]. split; [exact X3|].
unfold ztake. replace (Z.to_nat (sy_fill sy - sy_returned sy)) with 0%nat by lia. cbn. split; [reflexivity|].
replace (length (take 0 (zdrop (sy_returned sy) (sy_buf sy)))) with 0%nat by reflexivity. lia. }
1:{ rewrite Esd; reflexivity. }
1:{ rewrite Esd; split; [exact HIN| exact HK]. }
1:{ eapply (cmod_weaken _ _ (lb_remove_opt (sy_data sy) LB) _ (bv_unsigned sp) (bv_unsigned sp)); [rewrite Esd; eapply cmod_of_munch; [exact MU| exact WM]| lia| intros b Hb; exact Hb|].
intros x Hx; cbn in Hx |- *; lia. }
+
assert (Hpos : 0 < sy_fill sy - sy_returned sy) by lia.
zstep. zstep. zstep.

lazymatch type of MU with munch ?W2 m ?mx =>
pose proof (munch_weaken W2 [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 32); (D, D + sy_storage sy)] m mx
ltac:(unfold sub_fp; cbn [outside]; intros; lia) MU) as MU3 end.
clear MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (memmove_fwd_spec _ (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp _ _ _ _ _ (Z_to_bv 64 D) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx
D (sy_returned sy) (sy_fill sy - sy_returned sy) bytes) end.
all: try reflexivity. all: try (f_equal; lia). all: try lia.
all: try exact ARR. all: try assumption.
rename POST into ARR1. change X1fe.rsegs with rsegs in ARR1.
lazymatch goal with H : mem_inv X1fe.rsegs ?mm |- _ => change X1fe.rsegs with rsegs in H end.
remember (firstn (Z.to_nat (sy_fill sy - sy_returned sy)) (skipn (Z.to_nat (sy_returned sy)) bytes) ++ skipn (Z.to_nat (sy_fill sy - sy_returned sy)) bytes) as bytes1 eqn:Eb1 in ARR1.
assert (LENb1 : length bytes1 = length bytes).
{ rewrite Eb1. rewrite app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia). lia. }

zstep. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia).
lstep.
apply evt_done.
pose proof (compact_prefix (sy_buf sy) bytes (Z.to_nat (sy_returned sy)) (Z.to_nat (sy_fill sy - sy_returned sy)) X4
ltac:(unfold zlength in I2; lia) X5) as [PRE PREL].
eapply (buf_rest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st LB sy sy1 size A D lo B m _ errv _ bytes1);
try eassumption; try reflexivity; try lia.
1:{ eapply RHEAP_frame_proof; [exact HP| exact MU3| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|].
apply Forall_cons; [right; right; exists (p, D, sy_storage sy); split; [exact HIN| cbn; lia]|]. apply Forall_nil. }
1:{ eapply rauxv_ok_frame; [exact AUX| exact MU3| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
1:{ unfold sync_data; subst sy1; cbn -[Z.lt Z.of_nat ubytes Z.sub Z.to_nat firstn skipn app length ztake zdrop]; rewrite ?Esd.
split; [exact X1|]. split; [exact ARR1|].
split; [rewrite LENb1; lia|].
unfold ztake, zdrop. rewrite Eb1. split; [exact PRE| exact PREL]. }
1:{ rewrite ?Esd. first [reflexivity | exact Esd | cbn; rewrite ?Esd; reflexivity]. }
1:{ rewrite Esd. split; [exact HIN| exact HK]. }
1:{ eapply (cmod_weaken _ _ (lb_remove_opt (sy_data sy) LB) _ (bv_unsigned sp) (bv_unsigned sp)); [rewrite Esd; eapply cmod_of_munch; [exact MU3| exact WM]| lia| intros b Hb; exact Hb|].
intros xq Hxq; cbn in Hxq |- *; lia. }
Qed.
End BUFS.
