(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE p2 (lib/B/W_LLVMFuzzerTestOneInput_gone.v's GP2): the reads[] loop 0x84af8 -> 0x84b40
   (fuzz_reply.c:640-641 `reads[k] = g_s[k].open && relay_reads(&g_s[k])`), the image-B twin of
   lib/A/W_LLVMFuzzerTestOneInput_gone_p2.v (a working branch 32b23a20c3e), read from B's objdump:
     0x84af8  lb   a0,0(s9)           the shadow byte of g_s[q].open (s9 = SB + (g_s + 4) / 8 + 12q)
     0x84afc  bnez a0,84b30           the slow path (not reached: g_s lies in the instance's zero-shadow ranges,
                                      the base's GN_HZS, so the shadow byte is 0 and the report 0x85134 is dead)
     0x84b00  lw   a0,4(s6)           g_s[q].open (s6 = &g_s[q])
     0x84b04  beqz a0,84b10           the closed slot: reads[q] = 0
     0x84b08  mv   a0,s6
     0x84b0c  jal  864e8 <relay_reads>
     0x84b10  sw   a0,0(s8)           reads[q] at F + 192 + 4q
     0x84b14-0x84b24  s7--, s8 += 4, s6 += 96, s4 += 96, s9 += 12
     0x84b28  bnez s7,84af8           / 0x84b2c j 84b40
   B CALLS relay_reads where A inlines relay_reads / relay_source (the cut's difference (1)): the call is cited
   through the cut's RRDS (lib/B/W_LLVMFuzzerTestOneInput_cut.v:707 at 61da015af91), taken here as the Section hypothesis RRDS with
   the cut's text verbatim.  Its aleafx_post keeps every byte outside [F - RRDS_STK, F), which the arm's transport kit
   (W_LLVMFuzzerTestOneInput_gone_tk.v, gk_amodel_kept / gk_gframe_kept / gk_ainput_kept / gk_rom_kept / gk_jt_kept)
   turns into the cut's facts at 0x84b40; its a0 is matched with the base's gn_find / gn_src / gn_reads
   (g2_reads_of_post below).  The call pattern (afn_pre at sp = F through the base's gn_afn_pre, SRr_bind,
   ajournal_gx_G_mono + ajournal_gx_sub, the new entry state at the return pc) is B's latch walk's,
   lib/B/W_LLVMFuzzerTestOneInput_latch.v:785-990 at a working branch ee519e5e2f5. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the transport kit turns the euclidean-division equations off for lia; this file's shadow-pointer goals
   ((g_s + 96q + 4) / 8) need them, so they are on again here (A's p2 does the same). *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the phase's own address *)
Definition AF_gn_st : Z := 0x27cc.      (* 0x84b10: sw a0,0(s8), relay_reads's return site *)

(* the callee-saved registers the head keeps as atoms (s9 = 25 is pinned to the shadow pointer, so it is not in
   the list regs_kept_of_st_ok_pi checks; its value is read back with prreg) *)
Definition G2_CS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
(* the registers the tail keeps (all but s4, s6, s7, s8, s9) *)
Definition G2_K2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 26; 27]%bv.

(* ------------------------------------------------------------------ gn_find, as relay_reads's post gives it
   (A's p2 g2_find_none_from / g2_find_some_from, verbatim) *)
Lemma g2_find_none_from : forall es fd i,
  (forall u, (u < length es)%nat -> re_fd (nth u es gn_e0) <> fd) -> gn_find es fd i = None.
Proof.
  induction es as [|e es IH]; intros fd i HN; [reflexivity|].
  cbn [gn_find]. destruct (Z.eqb_spec (re_fd e) fd) as [Heq|_].
  - exfalso. apply (HN 0%nat ltac:(cbn [length]; lia)). cbn [nth]. exact Heq.
  - apply IH. intros u Hu. apply (HN (S u)). cbn [length]. lia.
Qed.
Lemma g2_find_some_from : forall es fd i0 i,
  (i0 < length es)%nat -> re_fd (nth i0 es gn_e0) = fd ->
  (forall u, (u < i0)%nat -> re_fd (nth u es gn_e0) <> fd) ->
  gn_find es fd i = Some (i + i0)%nat.
Proof.
  induction es as [|e es IH]; intros fd i0 i Hi0 Heq HN; cbn [length] in Hi0; [lia|].
  cbn [gn_find]. destruct i0 as [|i0].
  - cbn [nth] in Heq. rewrite Heq, Z.eqb_refl. f_equal. lia.
  - destruct (Z.eqb_spec (re_fd e) fd) as [Hbad|_].
    + exfalso. apply (HN 0%nat ltac:(lia)). cbn [nth]. exact Hbad.
    + rewrite (IH fd i0 (S i) ltac:(lia) Heq ltac:(intros u Hu; apply (HN (S u)); lia)). f_equal. lia.
Qed.
Lemma g2_nth_of_error : forall (l : list rentry) n e,
  nth_error l n = Some e -> (n < length l)%nat /\ nth n l gn_e0 = e.
Proof.
  induction l as [|x l IH]; intros [|n] e H; cbn [nth_error length nth] in H |- *; try discriminate.
  - injection H as <-. split; [lia | reflexivity].
  - destruct (IH n e H) as [H1 H2]. split; [lia | exact H2].
Qed.
Lemma g2_error_of_nth : forall (l : list rentry) n, (n < length l)%nat -> nth_error l n = Some (nth n l gn_e0).
Proof.
  induction l as [|x l IH]; intros [|n] H; cbn [nth_error length nth] in H |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed.
(* the shadow pointer s9 holds, in any env that agrees with the entry's on s4 (atom 20) and s11 (atom 27) *)
Lemma g2_USH : forall (Ev : env) (A : Z),
  ew Ev 27 = Z_to_bv 64 SB -> ew Ev 20 = Z_to_bv 64 (A + 4) -> 0 <= A -> A + 4 < 2 ^ 32 ->
  U Ev (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))) = SB + (A + 4) / 8.
Proof.
  intros Ev A E27 E20 H0 H1.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HDlo : 0 <= (A + 4) / 8) by (apply Z.div_pos; lia).
  assert (HDhi : (A + 4) / 8 <= A + 4) by (apply Z.div_le_upper_bound; lia).
  rewrite !U_SAlu, (U_atom Ev 27 SB E27), (U_atom Ev 20 _ E20), U_lit by lia.
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8. unfold zcanon, M64.
  rewrite (Z.mod_small ((A + 4) / 8)) by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
(* the shadow pointer the loop keeps in s9 *)
Lemma g2_shift : forall (q : nat), (q < 4)%nat ->
  (rg_s fr_RG + ASRC * Z.of_nat q + 4) / 8 = (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q.
Proof.
  intros q Hq.
  assert (Hrs : rg_s fr_RG = 6131296) by reflexivity.
  assert (Has : ASRC = 96) by reflexivity.
  rewrite Hrs, Has.
  replace (6131296 + 96 * Z.of_nat q + 4) with ((766412 + 12 * Z.of_nat q) * 8 + 4) by lia.
  replace (6131296 + 4) with (766412 * 8 + 4) by lia.
  rewrite !Z.div_add_l by lia. change (4 / 8) with 0. lia.
Qed.

Section gp2aux.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.

(* zero-shadow ranges, narrowed (A's p2 g2_azs_sub) *)
Lemma g2_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2.
  exists r. split; [exact Hin|]. split; [exact H8|]. split; lia.
Qed.
(* the open flag of slot i, and its model value (A's p2 g2_slot_at, at B's asrc_at) *)
Definition g2_sopen (o : option hsrc) : Z := match o with Some _ => 1 | None => 0 end.
Lemma g2_zero4 : forall (W : world segs) mem HA off,
  garr8 segs (arm W mem) HA (repeat 0 (Z.to_nat ASRC)) -> 0 <= off -> off + 4 <= ASRC ->
  val_mem segs (arm W mem) (HA + off) 4 0.
Proof.
  intros W mem HA off Hz Hlo Hhi kk Hk.
  assert (Hj : (Z.to_nat (off + Z.of_nat kk) < length (repeat 0 (Z.to_nat ASRC)))%nat)
    by (rewrite repeat_length; unfold ASRC in *; lia).
  pose proof (garr8_mbyte segs (arm W mem) HA _ _ Hz Hj) as Hb. rewrite nth_repeat in Hb.
  replace (HA + Z.of_nat (Z.to_nat (off + Z.of_nat kk))) with (HA + off + Z.of_nat kk) in Hb by lia.
  rewrite Hb. f_equal.
  destruct kk as [|[|[|[|kk]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
Qed.
Lemma g2_slot_open : forall ly S (W : world segs) mem i o,
  aslot B ly S W mem i o ->
  val_mem segs (arm W mem) (rg_s fr_RG + ASRC * Z.of_nat i + 4) 4 (g2_sopen o).
Proof.
  intros ly S W mem i [h|] Hs; cbn [aslot g2_sopen] in *.
  - pose proof Hs as (_ & H2 & _ & _ & _ & _ & _ & H8 & _). rewrite H8 in H2. exact H2.
  - destruct Hs as [Hz _].
    exact (g2_zero4 W mem (rg_s fr_RG + ASRC * Z.of_nat i) 4 Hz ltac:(lia) ltac:(unfold ASRC; lia)).
Qed.
Lemma g2_reads_rng : forall m (q : nat), 0 <= gn_reads m q <= 1.
Proof.
  intros m q. unfold gn_reads. destruct (nth q (lm_hs m) None) as [h|]; [|lia].
  destruct (gn_src m (hs_fd h)) as [i|]; [|lia].
  destruct (re_eof (nth i (lm_es m) gn_e0) =? 0); lia.
Qed.
(* relay_reads's a0, as the base's gn_reads reads it *)
Lemma g2_reads_of_post : forall m (q : nat) h (a0 : word),
  nth q (lm_hs m) None = Some h ->
  ((exists j e, nth_error (lm_es m) j = Some e /\ re_fd e = hs_fd h /\
      (forall i e', (i < j)%nat -> nth_error (lm_es m) i = Some e' -> re_fd e' <> hs_fd h) /\
      a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
   ((forall e, In e (lm_es m) -> re_fd e <> hs_fd h) /\ a0 = w64 0)) ->
  a0 = w64 (gn_reads m q).
Proof.
  intros m q h a0 Hnth [(j & e & Hj & Hfd & Hfirst & ->) | (Hno & ->)].
  - destruct (g2_nth_of_error (lm_es m) j e Hj) as [Hjl Hje].
    unfold gn_reads, gn_src. rewrite Hnth.
    rewrite (g2_find_some_from (lm_es m) (hs_fd h) j 0 Hjl ltac:(rewrite Hje; exact Hfd)
      ltac:(intros u Hu; apply (Hfirst u (nth u (lm_es m) gn_e0) Hu); apply g2_error_of_nth; lia)).
    cbn [Nat.add]. rewrite Hje. reflexivity.
  - unfold gn_reads, gn_src. rewrite Hnth.
    rewrite (g2_find_none_from (lm_es m) (hs_fd h) 0
      ltac:(intros u Hu; apply Hno; apply nth_In; exact Hu)).
    reflexivity.
Qed.
(* a byte kept, reflexively and transitively (A's p4 gp4_abk_refl / gp4_abk_trans) *)
Lemma g2_abk_refl : forall (W : world segs) mem a, abyte_kept W mem W mem a.
Proof. intros W mem a. split; [reflexivity | intros H; exact H]. Qed.
Lemma g2_abk_trans : forall (W1 W2 W3 : world segs) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof.
  intros W1 W2 W3 m1 m2 m3 a [A1 A2] [B1 B2]. split; [rewrite B1; exact A1 | intros H; exact (B2 (A2 H))].
Qed.
(* a byte present before a run that only grows the memory is present after it (A's p2 / B's p0) *)
Lemma g2_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
(* a callee-saved register across the call (B's latch lt_pres) *)
Lemma g2_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma g2_cs_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r (25%bv :: G2_CS) -> getr regs' r = getr regs r.
Proof.
  intros regs regs' HP r Hr. apply g2_pres; [exact HP|]. unfold G2_CS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?r] =>
       let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia |]).
  destruct Hr.
Qed.
(* the frame's prefix across a step that keeps the fake frame's bytes (A's p4 gp4_prefix_kept) *)
Lemma g2_prefix_kept : forall cx m (W W' : world segs) mem mem' FF,
  gn_prefix_at cx m W mem FF -> (forall a, FF + 32 <= a < FF + 80 -> abyte_kept W mem W' mem' a) ->
  gn_prefix_at cx m W' mem' FF.
Proof.
  intros cx m W W' mem mem' FF (P1 & P2 & P3 & P4 & P5) HK.
  split; [intros i Hi; rewrite (proj1 (HK (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
  split; [rewrite (proj1 (HK (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
  split; [intros a Ha; rewrite (proj1 (HK a Ha)); exact (P3 a Ha)|].
  split; [exact P4 | exact P5].
Qed.
End gp2aux.

(* ------------------------------------------------------------------ the entry states of the two runs *)
Definition g2_Bx : sv := SOff 27 0.
Definition g2_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* 0x84af8: s9 (reg 25) holds Shadow(&g_s[q].open) = SB + (s4 >> 3), the only compound register the engine needs;
   the slot's open field is read through s6 (reg 22) *)
Definition g2_sr_head : list sv :=
  sr_set sr_atoms 25 (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))).
Definition g2_rg_head : smem :=
  [ YP09.mkRegion (Some 22%nat) 4 8 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0))] ].
Definition g2_f_head : facts :=
  mkFacts [ (20%nat, mkAF (rg_s fr_RG + 4) (rg_s fr_RG + 3 * ASRC + 4) 2);
            (22%nat, mkAF (rg_s fr_RG) (rg_s fr_RG + 3 * ASRC) 5);
            (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 1 0) ] [] [].
Definition ss_g2_head : sstate := mkSS AF_gn_l1 g2_sr_head g2_rg_head None g2_f_head.
Definition g2_SH_head : list shent := [ mkSHE 20 0 8 ].
Definition g2_x_head (open : Z) : list word := map (Z_to_bv 64) [open].
(* 0x84b10: the store of reads[q] into the caller's own frame cell F + 192 + 4q *)
Definition g2_rg_tail : smem := [ YP09.mkRegion (Some 24%nat) 0 4 0 4 [] ].
Definition g2_f_tail : facts :=
  mkFacts [ (10%nat, mkAF 0 1 0); (23%nat, mkAF 1 4 0);
            (24%nat, mkAF (2 ^ 46) (2 ^ 47) 2); (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_g2_tail : sstate := mkSS AF_gn_st sr_atoms g2_rg_tail None g2_f_tail.

(* a register of the state after a run, with its symbolic value left raw (A's p2 g2_reg / g2_U: prreg's
   normalisation would hide the pinned shadow pointer) *)
Ltac g2_reg HS r H :=
  pose proof (st_ok_pi_restrict_reg (PI := PB_fr) _ _ _ _ (r : bv 5) HS) as H;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) (r : bv 5)) in
    change (sr_get (ss_regs ss) (r : bv 5)) with e in H end;
  cbn [ms_regs restrict mkst] in H.
Ltac g2_U := apply bv_eq;
  lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) = _ =>
    change (bv_unsigned (sv_denot Ev e)) with (U Ev e) end.
(* a register the tail bumped by a constant *)
Ltac g2_off Q nn cc HEq :=
  rewrite Q; g2_U;
  lazymatch goal with |- U ?Ev _ = _ =>
    rewrite (U_atom_off Ev nn _ cc ltac:(rewrite ?ew_ewset_other by lia; exact HEq)) by lia end;
  unfold w64; rewrite unsigned_lit_small by lia; lia.

Section gp2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* g_s lies in the instance's zero-shadow ranges: the base's model obligation, verbatim (the shadow byte of
   g_s[q].open at 0x84af8 is 0, so the slow path 0x84b30 and the report 0x85134 are not reached) *)
Hypothesis HZS : GN_HZS B.
(* errno's place: the base's model obligation, verbatim (amodel_at's aout_at reads errno across the call) *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* relay_reads (0x864e8): the cut's RRDS (lib/B/W_LLVMFuzzerTestOneInput_cut.v:707 at 61da015af91), text verbatim *)
Hypothesis RRDS : forall W ly S (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre segs B RRDS_STK ly S W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
  asrc_at B ly S W mem HA h ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
    (aleafx_post B RRDS_STK regs ly S W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* a run over read-only regions leaves the memory as it was *)
Ltac g2_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* ------------------------------------------------------------------ 0x84af8 -> 0x84b10: the open test and,
   for an open slot, relay_reads(&g_s[q]).  The post is the state at the return site, with a0 = reads[q]. *)
Definition g2_mid (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (v : Z) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk',
    c' = cfg_at segs (fr_B0 + AF_gn_st) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W' mem' md' kk' /\
    (forall r, In r G2_CS -> getr regs' r = getr regs r) /\
    getr regs' 25 = getr regs 25 /\ getr regs' 10 = w64 v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - RRDS_STK <= a < lf_F cx) -> abyte_kept W mem W' mem' a).

Lemma g2_head : forall cx (q : nat) m fpos ly S kk (W : world segs) regs mem md,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  amodel_at B ly S W mem m -> rom_view segs W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) ->
  getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) ->
  getr regs 27 = w64 SB ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_l1) regs mem md)
    (g2_mid cx fpos ly S (gn_reads m q) W regs mem).
Proof.
  intros cx q m fpos ly S kk W regs mem md HB HJ HSV HMOD HROM Hq R2 R3 R4 R8 R20 R22 R25 R27.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S W mem md kk fpos
                HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (HD2lo : 0 <= (rg_s fr_RG + 4) / 8) by (apply Z.div_pos; lia).
  assert (HD2hi : (rg_s fr_RG + 4) / 8 <= rg_s fr_RG + 4) by (apply Z.div_le_upper_bound; lia).
  set (open := g2_sopen (nth q (lm_hs m) None)) in *.
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  pose proof (g2_slot_open B ly S W mem q (nth q (lm_hs m) None) (HSL q ltac:(lia))) as Mopen.
  assert (Hopen01 : 0 <= open <= 1) by (unfold open, g2_sopen; destruct (nth q (lm_hs m) None); lia).
  assert (HZSA : azs B (rg_s fr_RG + ASRC * Z.of_nat q + 4) 8)
    by (apply (g2_azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
  (* RRDS's shadow premise (cut 61da015af91): g_s[q]'s first four bytes, a sub-range of GN_HZS *)
  assert (HZS4 : azs B (rg_s fr_RG + ASRC * Z.of_nat q) 4)
    by (apply (g2_azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
  assert (HSH : (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q = (rg_s fr_RG + ASRC * Z.of_nat q + 4) / 8)
    by (rewrite (g2_shift q Hq); reflexivity).
  set (A := rg_s fr_RG + ASRC * Z.of_nat q) in *.
  assert (HAe : A = 6131296 + 96 * Z.of_nat q) by (unfold A; rewrite HRS, HAS; reflexivity).
  assert (HA32 : A mod 32 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q) with ((191603 + 3 * Z.of_nat q) * 32) by lia;
        apply Z_mod_mult).
  assert (HA8 : A mod 8 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q) with ((766412 + 12 * Z.of_nat q) * 8) by lia;
        apply Z_mod_mult).
  assert (HA4 : (A + 4) mod 4 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q + 4) with ((1532825 + 24 * Z.of_nat q) * 4) by lia;
        apply Z_mod_mult).
  assert (HDlo : 0 <= (A + 4) / 8) by (apply Z.div_pos; lia).
  assert (HDhi : (A + 4) / 8 <= A + 4) by (apply Z.div_le_upper_bound; lia).
  assert (R25A : getr regs 25 = w64 (SB + (A + 4) / 8)) by (rewrite R25; unfold w64; f_equal; lia).
  (* the entry state *)
  remember (Eimg (Ereg regs (g2_x_head open))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (g2_x_head open)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (A + 4)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E22 : ew E 22 = Z_to_bv 64 A) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 open)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U20 : bv_unsigned (ew E 20) = A + 4) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = A) by (rewrite E22; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite E27; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = open) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_g2_head
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_l1)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_g2_head. apply pa_entry_st_ok_full.
    - unfold g2_sr_head. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]; rewrite <- HE.
      rewrite R25A. symmetry. apply bv_eq.
      change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))))
        with (U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
      rewrite (g2_USH E A E27 E20 ltac:(lia) ltac:(lia)).
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - vm_compute. reflexivity.
    - unfold g2_rg_head. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ A 4 4 (SOff 32 0) open);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Mopen.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_head f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U20, U22, U27, U32.
      change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end;
        first [lia | exact HA4 | exact HA32 | reflexivity]. }
  assert (HBx : U E g2_Bx = SHADOW_OFF).
  { unfold U, g2_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity. }
  assert (UA20 : U E (SOff 20 0) = A + 4).
  { unfold U. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity. }
  assert (SHOK : sh_ok segs g2_Bx g2_SH_head E (mrestrict (w_H W) mem)).
  { unfold sh_ok, g2_SH_head. constructor; [|constructor].
    eapply shent_ok_of_range.
    - exact (azs_range_addressable B LAWS ly S W mem md (A + 4) 8 HAR HZSA).
    - exact HBx.
    - exact UA20.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. lia. }
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1)).
  (* 0x84af8-0x84b00: the shadow byte (0), the slow-path test (not taken), g_s[q].open *)
  paj_run_tok RUN HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                         | apply awr_ok_x_nil]. }
  g2_mem HF Em1. clear HF HFr HG0.
  (* 0x84b04 beqz a0: the closed slot, or the call *)
  psrr_branch_tok RUN BR HS SHOK g2_span.
  - (* g_s[q].open = 0: reads[q] = 0, already at 0x84b10 *)
    rewrite branch_eq_U, (U_atom E 32 open E32), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    assert (Hnone : nth q (lm_hs m) None = None).
    { unfold open, g2_sopen in Hc. destruct (nth q (lm_hs m) None) as [h|]; [lia | reflexivity]. }
    assert (Hr0 : gn_reads m q = 0) by (unfold gn_reads; rewrite Hnone; reflexivity).
    (* 0x84b04 -> 0x84b10 *)
    paj_run_to_tok RUNTO HS HJ SHOK g2_span AF_gn_st.
    { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                           | apply awr_ok_x_nil]. }
    g2_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (g2_x_head open)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (10%bv : bv 5) Q10. g2_reg HS (25%bv : bv 5) Q25.
    assert (Q25v : getr (ms_regs ms0) 25 = w64 (SB + (A + 4) / 8)).
    { rewrite Q25. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (g2_USH Ev A ltac:(rewrite ?ew_ewset_other by lia; exact E27)
                               ltac:(rewrite ?ew_ewset_other by lia; exact E20)
                               ltac:(lia) ltac:(lia)) end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (Q10v : getr (ms_regs ms0) 10 = w64 (gn_reads m q)).
    { rewrite Q10, Hr0. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 32 open ltac:(rewrite ?ew_ewset_other by lia; exact E32)) by lia end.
      unfold open, g2_sopen. rewrite Hnone. unfold w64.
      rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. unfold g2_mid.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)); reflexivity|].
    split; [exact HJ|]. split; [exact KR|].
    split; [rewrite Q25v, R25A; reflexivity|].
    split; [exact Q10v|].
    intros a Ha Hno. apply g2_abk_refl.
  - (* g_s[q].open <> 0: the slot is open, and relay_reads(&g_s[q]) is called *)
    rewrite branch_eq_U, (U_atom E 32 open E32), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Hsome : exists h, nth q (lm_hs m) None = Some h).
    { unfold open, g2_sopen in Hc. destruct (nth q (lm_hs m) None) as [h|]; [exists h; reflexivity | lia]. }
    destruct Hsome as (h & Hsome).
    assert (HSRC : asrc_at B ly S W mem A h)
      by (pose proof (HSL q ltac:(lia)) as HSLq; rewrite Hsome in HSLq; exact HSLq).
    (* 0x84b08-0x84b0c: a0 = &g_s[q], jal relay_reads *)
    paj_run_to_tok RUNTO HS HJ SHOK g2_span AF_fr_relay_reads.
    { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                           | apply awr_ok_x_nil]. }
    g2_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (g2_x_head open)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. g2_reg HS (10%bv : bv 5) Q10. g2_reg HS (25%bv : bv 5) Q25.
    assert (Q25v : getr (ms_regs ms0) 25 = w64 (SB + (A + 4) / 8)).
    { rewrite Q25. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (g2_USH Ev A ltac:(rewrite ?ew_ewset_other by lia; exact E27)
                               ltac:(rewrite ?ew_ewset_other by lia; exact E20)
                               ltac:(lia) ltac:(lia)) end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (Q10v : getr (ms_regs ms0) 10 = w64 A).
    { rewrite Q10. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 22 A ltac:(rewrite ?ew_ewset_other by lia; exact E22)) by lia end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(cbv [G2_CS In]; tauto)), R2. unfold w64.
      apply unsigned_lit_small. lia. }
    destruct (gn_afn_pre B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG LS RINV
                cx ly S fpos kk W mem mdc rc0 RRDS_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(cbv [G2_CS In]; tauto)). exact R3. }
    { rewrite (KR 4%bv ltac:(cbv [G2_CS In]; tauto)). exact R4. }
    { rewrite (KR 8%bv ltac:(cbv [G2_CS In]; tauto)). exact R8. }
    { unfold RRDS_STK, RSRC_STK. lia. }
    { unfold RRDS_STK, RSRC_STK. lia. }
    eapply SRr_bind.
    { exact (RRDS W ly S rc0 mem mdc ch (lm_G m) (lm_es m) A h HPREc Q10v
               ltac:(lia) HA8 HZS4 HSRC HREL HROM). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HKEEP & HA0).
    rewrite Hsp1 in HJc, HKEEP.
    (* relay_reads's journal inside this function's: W2's ajournal_gx_sub at G_fr, the callee's lifted from G = [] *)
    assert (HJc' : ajournal_gx segs B G_fr 0 [] RRDS_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono segs B [] G_fr 0 [] RRDS_STK (lf_F cx) [] ly S W mem mdc []
                ly S W2 mem2 md2 0 _ HJc).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem mdc kk
       RRDS_STK (lf_F cx) 0 [] [] [] ly S W2 mem2 md2 0 HJ HJc'
       ltac:(unfold RRDS_STK, RSRC_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply SRr_ret. unfold g2_mid.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1;
            change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)); reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (g2_cs_pres rc0 regs2 HP2 r ltac:(right; exact Hr)); exact (KR r Hr)|].
    split; [rewrite (g2_cs_pres rc0 regs2 HP2 25%bv ltac:(left; reflexivity)), R25A; exact Q25v|].
    split.
    { rewrite (g2_reads_of_post m q h (getr regs2 10) Hsome HA0). reflexivity. }
    exact HKEEP.
Qed.

(* ------------------------------------------------------------------ 0x84b10 -> 0x84af8 / 0x84b40: the store of
   reads[q] into the frame cell F + 192 + 4q (no instrumented check: the cell is in the function's stack window),
   the five pointer bumps and the latch *)
Definition g2_tail_post (cx : lfcx) (fpos : Z) (ly : alayout) (Sa : astate) (q : nat) (v : Z)
    (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' kk',
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly Sa W mem' md' kk' /\
    (forall r, In r G2_K2 -> getr regs' r = getr regs r) /\
    val_mem segs (arm W mem') (lf_F cx + 192 + 4 * Z.of_nat q) 4 v /\
    (forall a, 0 <= a < 2 ^ 64 ->
       ~ (lf_F cx + 192 + 4 * Z.of_nat q <= a < lf_F cx + 192 + 4 * Z.of_nat q + 4) ->
       abyte_kept W mem W mem' a) /\
    (* the store cell stays writable too (every byte's writability is kept: the runs only grow presence) *)
    (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) /\
    getr regs' 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat (S q) + 4) /\
    getr regs' 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat (S q)) /\
    getr regs' 23 = w64 (4 - Z.of_nat (S q)) /\
    getr regs' 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat (S q)) /\
    getr regs' 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat (S q)) /\
    (((S q < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_l1) regs' mem' md') \/
     ((S q) = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_rig) regs' mem' md')).

Lemma g2_tail : forall cx (q : nat) fpos ly Sa kk (W : world segs) regs mem md v,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly Sa W mem md kk ->
  (q < 4)%nat -> 0 <= v <= 1 ->
  2 ^ 46 <= lf_F cx -> lf_F cx + 216 <= 2 ^ 47 -> lf_F cx mod 32 = 0 ->
  spZ (c_regs cx) - LLVMF_STK <= lf_F cx + 192 -> lf_F cx + 208 <= spZ (c_regs cx) ->
  awr W mem (lf_F cx + 192) 16 ->
  getr regs 10 = w64 v ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) ->
  getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 23 = w64 (4 - Z.of_nat q) ->
  getr regs 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) ->
  getr regs 27 = w64 SB ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_st) regs mem md) (g2_tail_post cx fpos ly Sa q v W regs mem).
Proof.
  intros cx q fpos ly Sa kk W regs mem md v HJ Hq Hv HF1 HF2 HF32 Hs1 Hs2 HW R10 R20 R22 R23 R24 R25 R27.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (HD2lo : 0 <= (rg_s fr_RG + 4) / 8) by (apply Z.div_pos; lia).
  assert (HD2hi : (rg_s fr_RG + 4) / 8 <= rg_s fr_RG + 4) by (apply Z.div_le_upper_bound; lia).
  set (cell := lf_F cx + 192 + 4 * Z.of_nat q) in *.
  assert (Hce : cell = lf_F cx + 192 + 4 * Z.of_nat q) by reflexivity.
  assert (Hc4 : cell mod 4 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
    replace cell with ((8 * (lf_F cx / 32) + 48 + Z.of_nat q) * 4) by lia. apply Z_mod_mult. }
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q + 4))
    by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E22 : ew E 22 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q))
    by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (4 - Z.of_nat q)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = Z_to_bv 64 cell) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = Z_to_bv 64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q))
    by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = 4 - Z.of_nat q) by (rewrite E23; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = cell) by (rewrite E24; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite E27; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_g2_tail
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_st)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_g2_tail. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold g2_rg_tail. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U24. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil].
      intros o Ho. replace (cell + o) with (lf_F cx + 192 + (4 * Z.of_nat q + o)) by lia.
      apply HW. lia.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_tail f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U10, U23, U24, U27.
      change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [lia | exact Hc4 | reflexivity]. }
  assert (SHOK : sh_ok segs g2_Bx (@nil shent) E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)).
  (* 0x84b10-0x84b24: the store and the five bumps *)
  paj_run_tok RUN HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
    left. split; [left; lia | lia]. }
  rename HF into HFst, HFr into HFrst, HG0 into HGst.
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms) a).
  { intros a Ha Hna. split.
    - apply (aview_kept_out _ _ _ _ _ HFrst a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_g2_tail g2_rg_tail In] in Hin.
      destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U24 in Hr. lia.
    - intros Hw. exact (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw). }
  (* 0x84b28 bnez s7: the next slot, or 0x84b2c j 84b40 *)
  psrr_branch_tok RUN BR HS SHOK g2_span.
  - (* 4 - q - 1 <> 0: back to the loop's head *)
    rewrite branch_ne_U, (U_atom_off E 23 _ (-1) ltac:(rewrite ?ew_ewset_other by lia; exact E23)), U_lit
      in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hq1 : (S q < 4)%nat) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK g2_span AF_gn_l1.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U24 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (cell + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 24%nat cell _ _ _ _ _ 0 4%N (SOff 10 0) v RG1) end.
      - rewrite ?ew_ewset_other by lia. exact U24.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms0)) cell 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms0) a).
    { intros a Ha Hna. apply (g2_abk_trans W W W mem (ms_mem ms) (ms_mem ms0) a (KEEP0 a Ha Hna)).
      split.
      - apply (aview_kept_out _ _ _ _ _ HFr a Ha).
        intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite U24 in Hr; lia.
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0) Hw). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0)
            (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw))).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (20%bv : bv 5) Q20. g2_reg HS (22%bv : bv 5) Q22. g2_reg HS (23%bv : bv 5) Q23.
    g2_reg HS (24%bv : bv 5) Q24. g2_reg HS (25%bv : bv 5) Q25.
    pmkst HS.
    apply SRr_ret. unfold g2_tail_post. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |}] => exists r, mm, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. split; [exact MV|]. split; [exact KEEP|]. split; [exact WK|].
    split; [g2_off Q20 20%nat 96 E20|].
    split; [g2_off Q22 22%nat 96 E22|].
    split; [g2_off Q23 23%nat (-1) E23|].
    split; [g2_off Q24 24%nat 4 E24|].
    split; [g2_off Q25 25%nat 12 E25|].
    left. split; [exact Hq1|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1)). reflexivity.
  - (* 4 - q - 1 = 0: 0x84b2c `j 84b40` *)
    rewrite branch_ne_U, (U_atom_off E 23 _ (-1) ltac:(rewrite ?ew_ewset_other by lia; exact E23)), U_lit
      in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hq4 : (S q) = 4%nat) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK g2_span AF_gn_rig.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U24 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (cell + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 24%nat cell _ _ _ _ _ 0 4%N (SOff 10 0) v RG1) end.
      - rewrite ?ew_ewset_other by lia. exact U24.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms0)) cell 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms0) a).
    { intros a Ha Hna. apply (g2_abk_trans W W W mem (ms_mem ms) (ms_mem ms0) a (KEEP0 a Ha Hna)).
      split.
      - apply (aview_kept_out _ _ _ _ _ HFr a Ha).
        intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite U24 in Hr; lia.
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0) Hw). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0)
            (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw))).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (20%bv : bv 5) Q20. g2_reg HS (22%bv : bv 5) Q22. g2_reg HS (23%bv : bv 5) Q23.
    g2_reg HS (24%bv : bv 5) Q24. g2_reg HS (25%bv : bv 5) Q25.
    pmkst HS.
    apply SRr_ret. unfold g2_tail_post. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |}] => exists r, mm, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. split; [exact MV|]. split; [exact KEEP|]. split; [exact WK|].
    split; [g2_off Q20 20%nat 96 E20|].
    split; [g2_off Q22 22%nat 96 E22|].
    split; [g2_off Q23 23%nat (-1) E23|].
    split; [g2_off Q24 24%nat 4 E24|].
    split; [g2_off Q25 25%nat 12 E25|].
    right. split; [exact Hq4|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)). reflexivity.
Qed.

(* the base's gframe across a call window [F - w, F) AND one 4-byte store at lo inside reads[] (F + 192 .. F + 208,
   which no sv8 of gframe names): tk's gk_gframe_kept with the store's cell excluded from the kept bytes and its
   writability given separately (the cell is inside gframe's awr F (sp0 - F)) *)
Lemma g2_gframe_kept : forall cx sh FF (W W' : world segs) mem mem' w lo,
  gframe cx sh FF W mem -> length sh = 16%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - w <= a < lf_F cx) -> ~ (lo <= a < lo + 4) ->
     abyte_kept W mem W' mem' a) ->
  (forall a, lo <= a < lo + 4 -> writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  lf_F cx + 192 <= lo -> lo + 4 <= lf_F cx + 208 ->
  0 <= w -> GK_CEIL8 <= lf_F cx - w -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= GK_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= GK_CEIL8 ->
  gframe cx sh FF W' mem'.
Proof.
  intros cx sh FF W W' mem mem' w lo
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20
     & A21 & A22) Hsh HK HWK Hlo1 Hlo2 Hw0 HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof gk_ceil_hi as HC64. pose proof gk_ceil_lo as HCL.
  assert (HFpos : 0 <= lf_F cx) by (unfold GK_CEIL8 in *; lia).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) by (intros a Ha; apply HK; lia).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> ~ (lo <= a < lo + 4) -> abyte_kept W mem W' mem' a)
    by (intros a Ha Hn; apply HK; [lia | lia | exact Hn]).
  split.
  { intros o r Hin. apply (gk_sv8_kept W W' mem mem'); [|exact (A1 o r Hin)].
    intros x Hx.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    apply KH; lia. }
  split.
  { intros i Hi.
    destruct (Z_lt_le_dec (lf_F cx + i) lo) as [H1 | H1];
      [| destruct (Z_lt_le_dec (lf_F cx + i) (lo + 4)) as [H2 | H2]].
    - apply (proj2 (KH (lf_F cx + i) ltac:(lia) ltac:(lia))). exact (A2 i Hi).
    - apply HWK; [lia | exact (A2 i Hi)].
    - apply (proj2 (KH (lf_F cx + i) ltac:(lia) ltac:(lia))). exact (A2 i Hi). }
  do 14 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | assumption]|]).
  do 3 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact A20]|].
  split.
  { apply (akept_garr8 W mem); [|exact A21]. intros x Hx.
    rewrite Hsh in Hx. apply KL. lia. }
  apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact A22].
Qed.

(* ------------------------------------------------------------------ one trip of the reads[] loop *)
Lemma g2_step : forall (q : nat) cx t m W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  GL1 B G_fr fr_FP LS RINV cx t m q W c ->
  SRr segs W c (fun W' c' => GL1 B G_fr fr_FP LS RINV cx t m (S q) W' c' \/
                             GRG B G_fr fr_FP LS RINV cx t m W' c').
Proof.
  intros q cx t m W c HB HL1.
  destruct HL1 as (regs & mem & md & ly & St & kk & fpos & Hc & HGST & HLS & HRI & HOP & HKR &
                   R26 & R21 & R22 & R20 & R23 & R24 & R25 & Hq & HCELLS & HAWR & HAT & HPRE).
  destruct HGST as (HCOM & HMOD & HSEP).
  destruct HCOM as (HJ & HFRM & HFL & HP16 & HN144 & HT88 & HIN & HROM & HJT).
  pose proof HKR as (K2 & K8 & K9 & K18 & K19 & K27 & K3 & K4).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly St W mem md kk fpos
                HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  pose proof YM05.alloc_ceiling_value as AC. pose proof gk_ceil_lo as HCL0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE2). pose proof HPRE2 as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof HERR as (HE0 & HE1).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (HCEIL : GK_CEIL8 = alloc_ceiling + 8) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HRSTK : RRDS_STK = 32) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (HFFs : 0 <= SB + FF / 8 /\ SB + FF / 8 + 16 <= GK_CEIL8).
  { pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hd1.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd2. lia. }
  rewrite Hc.
  (* 0x84af8 -> 0x84b10 *)
  eapply SRr_bind.
  { exact (g2_head cx q m fpos ly St kk W regs mem md HB HJ (proj1 HFRM) HMOD HROM Hq
             K2 K3 K4 K8 R20 R22 R25 K27). }
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & K25a & R10a & KP1).
  (* what the call kept *)
  assert (KH : forall a, F <= a < 2 ^ 64 -> abyte_kept W mem W1 mem1 a)
    by (intros a Ha; apply KP1; lia).
  assert (HAWR1 : awr W1 mem1 (F + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]).
  (* 0x84b10 -> 0x84af8 / 0x84b40 *)
  eapply SRr_bind.
  { apply (g2_tail cx q fpos ly St kk1 W1 regs1 mem1 md1 (gn_reads m q) HJ1 Hq (g2_reads_rng m q));
      [ lia | lia | exact HF32 | lia | lia | exact HAWR1 | exact R10a
      | rewrite (KR1 20%bv ltac:(cbv [G2_CS In]; tauto)); exact R20
      | rewrite (KR1 22%bv ltac:(cbv [G2_CS In]; tauto)); exact R22
      | rewrite (KR1 23%bv ltac:(cbv [G2_CS In]; tauto)); exact R23
      | rewrite (KR1 24%bv ltac:(cbv [G2_CS In]; tauto)); exact R24
      | rewrite K25a; exact R25
      | rewrite (KR1 27%bv ltac:(cbv [G2_CS In]; tauto)); exact K27 ]. }
  intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & kk2 & HJ2 & KR2 & MV & KP2 & WK2 & Q20 & Q22 & Q23 & Q24 & Q25 & Hpc).
  (* the two steps composed *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F - RRDS_STK <= a < F) ->
      ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha Hn1 Hn2; exact (g2_abk_trans W W1 W1 mem mem1 mem2 a (KP1 a Ha Hn1) (KP2 a Ha Hn2))).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha; apply KEEP; lia).
  assert (KHI : forall a, F <= a < 2 ^ 64 ->
      ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha Hn2; apply KEEP; [lia | lia | exact Hn2]).
  (* the cut's facts at the next cut point *)
  assert (HMOD2 : amodel_at B ly St W1 mem2 m)
    by (exact (gk_amodel_kept B LAWS ly St W mem md W1 mem2 m HAR HMOD HE0 ltac:(lia) KL)).
  assert (HIN2 : ainput_at B cx ly St W1 mem2)
    by (exact (gk_ainput_kept B LAWS cx ly St W mem md W1 mem2 HAR HIN (eq_sym Hnlen) KL)).
  assert (HROM2 : rom_view segs W1 mem2) by (exact (gk_rom_kept W W1 mem mem2 HROM KL)).
  assert (HJT2 : jt_rom W1 mem2) by (exact (gk_jt_kept W W1 mem mem2 HJT KL)).
  assert (HFRM2 : gframe cx fake_shadow_open FF W1 mem2).
  { apply (g2_gframe_kept cx fake_shadow_open FF W W1 mem mem2 RRDS_STK (F + 192 + 4 * Z.of_nat q) HFRM eq_refl);
      [ intros a Ha Hn Hcl; apply KEEP; [exact Ha | exact Hn | exact Hcl]
      | intros a Ha Hw; apply WK2; exact (proj2 (KP1 a ltac:(lia) ltac:(lia)) Hw)
      | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia ]. }
  assert (HFL2 : sv8 W1 mem2 (FF + 120) (flag_addr ly 1 fpos))
    by (apply (gk_sv8_kept W W1 mem mem2); [intros x Hx; apply KL; lia | exact HFL]).
  assert (KV8 : forall a v, F <= a -> a + 8 <= 2 ^ 64 ->
      (a + 8 <= F + 192 + 4 * Z.of_nat q \/ F + 192 + 4 * Z.of_nat q + 4 <= a) ->
      sv8 W mem a v -> sv8 W1 mem2 a v)
    by (intros a v H0 H1 H3 Hv; apply (gk_sv8_kept W W1 mem mem2); [|exact Hv];
        intros x Hx; apply KHI; lia).
  assert (HP16' : sv8 W1 mem2 (F + 16) (c_p cx + gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HP16]).
  assert (HN144' : sv8 W1 mem2 (F + 144) (c_n cx - gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HN144]).
  assert (HT88' : sv8 W1 mem2 (F + 88) t)
    by (apply KV8; [lia | lia | left; lia | exact HT88]).
  assert (HAT' : sv8 W1 mem2 (F + 208) 0)
    by (apply KV8; [lia | lia | right; lia | exact HAT]).
  assert (HAWR' : awr W1 mem2 (F + 192) 16).
  { intros i Hi. apply WK2. exact (HAWR1 i Hi). }
  assert (HPRE' : gn_prefix_at cx m W1 mem2 FF).
  { apply (g2_prefix_kept cx m W W1 mem mem2 FF HPRE). intros a Ha. apply KL. lia. }
  assert (CELLS : forall j, (j < S q)%nat -> gn_sv4 W1 mem2 (F + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. destruct (Nat.eq_dec j q) as [->|Hne]; [exact MV|].
    apply (akept_vm W mem); [|exact (HCELLS j ltac:(lia))].
    intros x Hx. cbn in Hx. apply KHI; [lia|].
    assert (Hjz : 0 <= Z.of_nat j <= 3) by lia.
    assert (Hjq : Z.of_nat j <> Z.of_nat q) by lia. lia. }
  assert (KREGS : gn_kregs B cx FF regs2).
  { unfold gn_kregs. repeat split;
      first [ rewrite (KR2 2%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 2%bv ltac:(cbv [G2_CS In]; tauto)); exact K2
            | rewrite (KR2 8%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 8%bv ltac:(cbv [G2_CS In]; tauto)); exact K8
            | rewrite (KR2 9%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 9%bv ltac:(cbv [G2_CS In]; tauto)); exact K9
            | rewrite (KR2 18%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 18%bv ltac:(cbv [G2_CS In]; tauto)); exact K18
            | rewrite (KR2 19%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 19%bv ltac:(cbv [G2_CS In]; tauto)); exact K19
            | rewrite (KR2 27%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 27%bv ltac:(cbv [G2_CS In]; tauto)); exact K27
            | rewrite (KR2 3%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 3%bv ltac:(cbv [G2_CS In]; tauto)); exact K3
            | rewrite (KR2 4%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 4%bv ltac:(cbv [G2_CS In]; tauto)); exact K4 ]. }
  assert (R26' : getr regs2 26 = w64 HI_G_NOUT)
    by (rewrite (KR2 26%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 26%bv ltac:(cbv [G2_CS In]; tauto)); exact R26).
  assert (R21' : getr regs2 21 = w64 (gn_id cx m))
    by (rewrite (KR2 21%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 21%bv ltac:(cbv [G2_CS In]; tauto)); exact R21).
  apply SRr_ret.
  destruct Hpc as [(Hq1 & ->) | (Hq4 & ->)].
  - left. exists regs2, mem2, md2, ly, St, kk2, fpos.
    split; [reflexivity|].
    split; [split; [split; [exact HJ2|]; split; [exact HFRM2|]; split; [exact HFL2|];
                    split; [exact HP16'|]; split; [exact HN144'|]; split; [exact HT88'|];
                    split; [exact HIN2|]; split; [exact HROM2 | exact HJT2]|];
            split; [exact HMOD2 | exact HSEP]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R26'|]. split; [exact R21'|].
    split; [exact Q22|]. split; [exact Q20|]. split; [exact Q23|]. split; [exact Q24|].
    split; [exact Q25|].
    split; [exact Hq1|]. split; [exact CELLS|].
    split; [exact HAWR'|]. split; [exact HAT' | exact HPRE'].
  - right. exists regs2, mem2, md2, ly, St, kk2, fpos.
    split; [reflexivity|].
    split; [split; [split; [exact HJ2|]; split; [exact HFRM2|]; split; [exact HFL2|];
                    split; [exact HP16'|]; split; [exact HN144'|]; split; [exact HT88'|];
                    split; [exact HIN2|]; split; [exact HROM2 | exact HJT2]|];
            split; [exact HMOD2 | exact HSEP]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R26'|]. split; [exact R21'|].
    split; [intros j Hj; apply CELLS; lia|].
    split; [exact HAWR'|]. split; [exact HAT' | exact HPRE'].
Qed.

(* ------------------------------------------------------------------ the loop, by the trips left *)
Lemma g2_loop : forall (n q : nat) cx t m W c,
  (q + n = 4)%nat ->
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  GL1 B G_fr fr_FP LS RINV cx t m q W c ->
  SRr segs W c (GRG B G_fr fr_FP LS RINV cx t m).
Proof.
  induction n as [|n IH]; intros q cx t m W c Hn HB HL1.
  - exfalso. pose proof HL1 as (regs & mem & md & ly & St & kk & fpos & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & Hq & _). lia.
  - eapply SRr_bind; [exact (g2_step q cx t m W c HB HL1)|].
    intros W' c' _ [HL1' | HRG]; [exact (IH (S q) cx t m W' c' ltac:(lia) HB HL1') |].
    apply SRr_ret. exact HRG.
Qed.

(* ================================================================== GP2 of
   lib/B/W_LLVMFuzzerTestOneInput_gone.v: the reads[] loop, 0x84af8 -> 0x84b40 *)
Lemma gp2_l1_rig : forall q cx t m W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GL1 B G_fr fr_FP LS RINV cx t m q W c ->
  SRr segs W c (GRG B G_fr fr_FP LS RINV cx t m).
Proof.
  intros q cx t m W c HB HL1.
  pose proof HL1 as (regs & mem & md & ly & St & kk & fpos & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & Hq & _).
  exact (g2_loop (4 - q)%nat q cx t m W c ltac:(lia) HB HL1).
Qed.

End gp2.
