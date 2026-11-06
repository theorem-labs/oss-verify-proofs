From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09 YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Contract OutForm Img0.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr FP.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel KindB fread_c fread_ro_c memmove_c memmove_ro_c
  pcap_source_struct pcap_source_struct_next pcap_lib pcap_source_next_lib pcap_source_next_ep
  pcap_source_next_body pcap_source_next_skip pcap_source_next_iter pcap_source_next_ret pcap_source_next_c.
Import ListNotations YK11.
Open Scope Z_scope.

Definition hide (P : Prop) : Prop := P.

Ltac hide_hyp H := let T := type of H in change (hide T) in H.

Section K.
Context {fx : YK11.FPState}.

Lemma psn_evt_SRO : forall ms0 ms (Q : machine_state -> Prop) md out (P : config -> Prop),
  Regs6ss.ms_eqv ms0 ms -> Exec.evt rsegs Q ms0 -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall can ms', Q can -> Regs6ss.ms_eqv can ms' -> SRO rsegs (mkCfg ms' md) out P) ->
  SRO rsegs (mkCfg ms md) out P.
Proof.
  intros ms0 ms Q md out P EQ H Hh Hl K.
  apply (SR_SRO_bind rsegs (mkCfg ms md) out
           (fun c => exists ms' can, c = mkCfg ms' md /\ Q can /\ Regs6ss.ms_eqv can ms') P).
  - apply (evt_SR rsegs ms _ md _ (RegisterBridge.evt_register_transport rsegs Q ms0 ms EQ H) Hh Hl).
    intros ms' (can & HQ & HE). apply SR_ret. exists ms', can. split; [reflexivity|]. split; assumption.
  - intros c (ms' & can & -> & HQ & HE). exact (K can ms' HQ HE).
Qed.

Lemma eqv_mk : forall (gx : YK11.FPState) M R pc m ro, Regs6ss.xregs_eqv M R ->
  Regs6ss.ms_eqv (MS M (@YK11.fp_regs gx) pc (@YK11.fp_csr gx) None m ro) (@YK11.mkst gx R pc m ro).
Proof. intros gx M R pc m ro X. unfold Regs6ss.ms_eqv. split; [exact X | repeat split]. Qed.

Lemma psn_preserved : forall regs0 R (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Regs6ss.xregs_eqv (mkR x1 (getr regs0 2) (getr regs0 3) (getr regs0 4) x5 x6 x7 (getr regs0 8) (getr regs0 9)
    x10 x11 x12 x13 x14 x15 x16 x17 (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22)
    (getr regs0 23) (getr regs0 24) (getr regs0 25) (getr regs0 26) (getr regs0 27) x28 x29 x30 x31) R ->
  regs_preserved regs0 R.
Proof.
  intros regs0 R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 X r Hr.
  assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  rewrite (getr_of_eqv _ _ _ X NZ). unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

Lemma stk_frame : forall m lo A ph cs, stk rsegs m lo A -> rw_cells rsegs m A [CB 16 ph] ->
  rw_cells rsegs m (A + 16) cs -> cells_size cs = 80%nat -> lo <= A -> stk rsegs m lo (A + 96).
Proof.
  intros m lo A ph cs S P C N L.
  assert (S1 : stk rsegs m lo (A + 16)) by exact (stk_release rsegs m lo A [CB 16 ph] S P L).
  pose proof (stk_release rsegs m lo (A + 16) cs S1 C ltac:(lia)) as S2.
  rewrite N in S2. change (Z.of_nat 80) with 80 in S2.
  replace (A + 96) with (A + 16 + 80) by lia. exact S2.
Qed.

Lemma psn_eg : forall W m m' fl md, errf m fl md -> guard_ok m -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W A_STDERR 232 -> disjoint_from W A_GOT_GUARD 8 -> disjoint_from W A_GUARD 8 ->
  errf m' fl md /\ guard_ok m'.
Proof.
  intros W m m' fl md (E1 & E2 & E3) (G1 & g & G2) MU WM D1 D2 D3.
  split; [split; [exact (rw_cells_transport rsegs _ _ _ _ _ E1 MU WM D1) | split; assumption] | split].
  - exact (bytes_at_transport rsegs _ _ _ _ _ G1 MU ltac:(rewrite length_le8; exact D2)).
  - exists g. exact (bytes_at_transport rsegs _ _ _ _ _ G2 MU ltac:(rewrite length_le8; exact D3)).
Qed.

Lemma psn_mstl_q : forall m h b Fc q pv nx, mstl m h b Fc q pv nx -> (0 <= q <= Z.of_nat (length Fc)) /\ 0 < h /\ 0 < b.
Proof.
  intros m h b Fc q pv nx HMS.
  destruct HMS as (fl & md & q' & rb & (bf & (pd0 & pd1 & pd2 & ung & HC & L1 & L2 & H0 & H16) & Hq & Hrb & HFc & Hb0 & Hd)
                     & R1 & R2 & R3 & R4).
  destruct rb as [[i e]|]; cbn [rlen] in R3; lia.
Qed.

Definition psn_W (regs0 : bvmap 5 word) (ps buf cap ts h : Z) : list (Z * Z) :=
  [(spZ regs0 - NEXT_K, spZ regs0); (A_STDERR, A_STDERR + 232); (ps, ps + 24); (buf, buf + Z.max cap 1);
   (ts, ts + (if ts =? 0 then 0 else 8)); (h, h + 1304)].

Definition psn_res (sw : bool) (Fc : list byte) (cap q' : Z) (lh' : option Z) (mem' : word -> option byte)
    (ps buf ts h b swz : Z) (lol lvt lvid : word) (pad : list byte) (pv nx tsv : word) : Prop :=
  mstl mem' h b Fc (pos_of sw Fc cap q') pv nx /\
  rw_cells rsegs mem' ps (ps_cells (wz h) (wz swz) (lol_of sw Fc lh' lol) (vt_of sw Fc cap q' lvt)
                            (vid_of sw Fc cap q' lvid) pad) /\
  (exists bj', u8arr rsegs mem' buf bj' /\ Z.of_nat (length bj') = Z.max cap 1 /\
     (is_fit (kind sw Fc cap q') = true -> firstn (Z.to_nat (incl sw Fc q')) bj' = rec_bytes sw Fc q')) /\
  (ts <> 0 -> rw_cells rsegs mem' ts [C8 (ts_of sw Fc cap q' tsv)]).

Definition psn_fin (regs0 F0 : bvmap 5 word) (md : Model) (m : word -> option byte) (sw : bool) (Fc : list byte)
    (cap ps buf ts h b swz lo fl : Z) (lol lvt lvid : word) (pad : list byte) (pv nx tsv : word)
    (q' : Z) (lh' : option Z) (c' : config) : Prop :=
  exists regs' mem' (Ft : bvmap 5 word) (fc' : bv 32) (mdv' : Z),
    c' = mkCfg (@YK11.mkst (YK11.mkFP Ft fc') regs' (ret_pc (getr regs0 1)) mem' (seg_rom rsegs)) md /\
    frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F0 k) /\
    regs_preserved regs0 regs' /\ getr regs' 10 = wz (res_of sw Fc cap q') /\
    munch (psn_W regs0 ps buf cap ts h) m mem' /\
    wmono rsegs m mem' /\ errf mem' fl mdv' /\ guard_ok mem' /\ MemNorm.ro_agree rsegs mem' /\
    stk rsegs mem' lo (spZ regs0) /\
    psn_res sw Fc cap q' lh' mem' ps buf ts h b swz lol lvt lvid pad pv nx tsv.

Lemma psn_fin_pre : forall regs0 F0 md m m2 sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q' lh' c,
  munch (psn_W regs0 ps buf cap ts h) m m2 -> wmono rsegs m m2 ->
  psn_fin regs0 F0 md m2 sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q' lh' c ->
  psn_fin regs0 F0 md m sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q' lh' c.
Proof.
  intros regs0 F0 md m m2 sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q' lh' c MU WM
    (R & m' & Ft & fc' & mdv' & -> & H1 & H2 & H3 & H4 & MU' & WM' & H5).
  exists R, m', Ft, fc', mdv'. split; [reflexivity|]. do 4 (split; [assumption|]).
  split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans rsegs _ _ _ WM WM')|]. exact H5.
Qed.

Lemma psn_fin_exit : forall regs0 F0 md m sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q' lh'
    (gp tp s9 s10 s11 t0 t1 t2 rv a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (R Ft : bvmap 5 word) (fc' : bv 32) m' mdv',
  Regs6ss.xregs_eqv (mkR (getr regs0 1) (getr regs0 2) gp tp t0 t1 t2 (getr regs0 8) (getr regs0 9) rv a1 a2 a3 a4 a5 a6 a7
    (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24)
    s9 s10 s11 t3 t4 t5 t6) R ->
  gp = getr regs0 3 -> tp = getr regs0 4 -> s9 = getr regs0 25 -> s10 = getr regs0 26 -> s11 = getr regs0 27 ->
  rv = wz (res_of sw Fc cap q') ->
  frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F0 k) ->
  munch (psn_W regs0 ps buf cap ts h) m m' -> wmono rsegs m m' -> errf m' fl mdv' -> guard_ok m' ->
  MemNorm.ro_agree rsegs m' -> stk rsegs m' lo (spZ regs0) ->
  psn_res sw Fc cap q' lh' m' ps buf ts h b swz lol lvt lvid pad pv nx tsv ->
  psn_fin regs0 F0 md m sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q' lh'
    (mkCfg (@YK11.mkst (YK11.mkFP Ft fc') R (ret_pc (getr regs0 1)) m' (seg_rom rsegs)) md).
Proof.
  intros regs0 F0 md m sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q' lh'
    gp tp s9 s10 s11 t0 t1 t2 rv a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 R Ft fc' m' mdv' X -> -> -> -> -> -> FR FA MU WM EF GU RO
    ST RES.
  exists R, m', Ft, fc', mdv'. split; [reflexivity|]. split; [exact FR|]. split; [exact FA|].
  split; [exact (psn_preserved regs0 R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|].
  split; [exact (getr_of_eqv _ _ 10 X eq_refl)|].
  do 6 (split; [assumption|]). exact RES.
Qed.

Lemma psn_loop : fread_ro_contract -> memmove_ro_contract ->
  forall (n : nat) (regs0 F0 : bvmap 5 word) (md : Model) (sw : bool) (Fc : list byte)
    (cap ps buf ts h swz b lo fl : Z) (lol lvt lvid pv nx tsv : word) (pad : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ms : machine_state)
    (q : Z) (lh : option Z) (bj ph : list byte) (mdv : Z),
    Z.of_nat (length Fc) - q < Z.of_nat n ->
    Regs6ss.ms_eqv (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x50)%Z)) fc None m (seg_rom rsegs)) ms ->
    s0 = wz ts -> s1 = wz ps -> s2 = wz buf -> s4 = wz cap -> s7 = wz 16 -> s8 = wz 0xff00 -> a3 = wz h ->
    sw = (swz =? 1) ->
    gp = getr regs0 3 -> tp = getr regs0 4 -> s9 = getr regs0 25 -> s10 = getr regs0 26 -> s11 = getr regs0 27 ->
    bv_unsigned sp = spZ regs0 - 96 ->
    rw_cells rsegs m (bv_unsigned sp) [CB 16 ph] ->
    rw_cells rsegs m (bv_unsigned sp + 16)
      [C8 (getr regs0 24); C8 (getr regs0 23); C8 (getr regs0 22); C8 (getr regs0 21); C8 (getr regs0 20);
       C8 (getr regs0 19); C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 5632 <= bv_unsigned sp -> (symaddr ImgPages.Plain.top) <= lo ->
    spZ regs0 <= ps -> rw_cells rsegs m ps (ps_cells (wz h) (wz swz) (lol_of sw Fc lh lol) lvt lvid pad) ->
    (swz = 0 \/ swz = 1) ->
    mstl m h b Fc q pv nx -> img_apart h 1304 -> h + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    Z.of_nat (length Fc) < 2 ^ 26 ->
    0 <= cap < 2 ^ 64 -> 4096 <= buf -> u8arr rsegs m buf bj -> Z.of_nat (length bj) = Z.max cap 1 ->
    img_apart buf (Z.max cap 1) -> buf + Z.max cap 1 <= lo ->
    (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) -> (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length Fc) <= buf) ->
    (ts <> 0 -> spZ regs0 <= ts /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\ rw_cells rsegs m ts [C8 tsv]) ->
    0 <= ts < 2 ^ 64 ->
    errf m fl mdv -> guard_ok m -> MemNorm.ro_agree rsegs m ->
    frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
    m_halted md = None -> m_vm_lazy md = [] ->
    SRO rsegs (mkCfg ms md) (snd (fst (chain sw Fc cap n q lh)))
      (psn_fin regs0 F0 md m sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv
         (fst (fst (chain sw Fc cap n q lh))) (snd (chain sw Fc cap n q lh))).
Proof.
  intros HFR HMM n. induction n as [|f IH];
  intros regs0 F0 md sw Fc cap ps buf ts h swz b lo fl lol lvt lvid pv nx tsv pad
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ms q lh bj ph mdv
    HN EQ E0 E1 E2 E4 E7 E8 EA3 ESW EGP ETP ES9 ES10 ES11 Hsp HPH HSV ST LO HLO HPS0 HPS HSW HMS HIH HHL HBL HN26
    HCAP HB4K HBJ HBN HIB HBL2 HBH HBB HTS HTR EF GU RO FR FA Hh Hl.
  { exfalso. pose proof (psn_mstl_q _ _ _ _ _ _ _ HMS) as ((HQ0 & HQ1) & _ & _). lia. }
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs _ _ _ HPS) as HPR. cbn [cells_size csize ps_cells Nat.add] in HPR.
  pose proof (u8arr_len _ _ _ HBJ) as HBR.
  pose proof (psn_mstl_q _ _ _ _ _ _ _ HMS) as ((HQ0 & HQ1) & HH0 & HB0).
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof HIH as HIH'. pose proof HIB as HIB'. unfold img_apart in HIH', HIB'.
  pose proof Hsp as Hsp'. pose proof HPS0 as HPS0'. unfold spZ in Hsp', HPS0'.
  assert (TSD : ts = 0 \/ spZ regs0 <= ts)
    by (destruct (Z.eq_dec ts 0) as [T|T]; [left; exact T | right; exact (proj1 (HTS T))]).
  assert (TSB : 0 <= (if ts =? 0 then 0 else 8) <= 8) by (destruct (ts =? 0); lia).
  hide_hyp HSW. hide_hyp HBH. hide_hyp HBB. hide_hyp HTS.
  assert (STF : forall mm pp, stk rsegs mm lo (bv_unsigned sp) -> rw_cells rsegs mm (bv_unsigned sp) [CB 16 pp] ->
            rw_cells rsegs mm (bv_unsigned sp + 16)
              [C8 (getr regs0 24); C8 (getr regs0 23); C8 (getr regs0 22); C8 (getr regs0 21); C8 (getr regs0 20);
               C8 (getr regs0 19); C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)] ->
            stk rsegs mm lo (spZ regs0)).
  { intros mm pp S1 P1 C1. replace (spZ regs0) with (bv_unsigned sp + 96) by lia.
    exact (stk_frame mm lo _ pp _ S1 P1 C1 eq_refl ltac:(lia)). }
  eapply psn_evt_SRO; [exact EQ | | exact Hh | exact Hl |].
  { exact (psn_iter HFR HMM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m ps buf cap ts h swz b q lo sw Fc pv nx (lol_of sw Fc lh lol) lvt lvid tsv bj ph pad
             (getr regs0 2) (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20)
             (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24)
             E0 E1 E2 E4 E7 E8 EA3 ESW Hsp HPH HSV ST LO HLO HPS0 HPS HSW HMS HIH HHL HBL HN26 HCAP HB4K HBJ HBN
             HIB HBL2 HBH HBB HTS HTR RO). }
  intros can ms' POST EQ'.
  destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s5' & s6' & t3' & t4'
    & t5' & t6' & m' & DISJ & MU & WM & RO' & ST' & (ph' & PH') & HSV').
  assert (MUW : munch (psn_W regs0 ps buf cap ts h) m m')
    by (clear - MU Hsp; eapply munch_weaken; [| exact MU]; unfold sub_fp, psn_W, NEXT_K; out_tac).
  destruct (psn_eg _ _ _ _ _ EF GU MU WM ltac:(unfold A_STDERR; disj_tac) ltac:(unfold A_GOT_GUARD; disj_tac)
              ltac:(unfold A_GUARD; disj_tac)) as [EF' GU'].
  destruct DISJ as [(KX & -> & MSx & HPSx & (bjx & HBJx & LBx & FBx) & HTSx) |
                    [(KE & -> & MSe & HPSe & HBJe & HTSe) | (KB & -> & MSb & HPSb & HBJb & HTSb)]].
  - hide_hyp HTSx. rewrite (chain_exit sw Fc cap f q lh KX). cbn [fst snd].
    apply SRO_ret.
    destruct (@eqv_mkst (YK11.mkFP F fc) _ _ _ _ _ _ _ EQ' eq_refl eq_refl) as (R' & -> & X').
    apply (psn_fin_exit regs0 F0 md m sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q
             (if hdr_kind (kind sw Fc cap q) then Some q else lh) gp tp s9 s10 s11 t0' t1' t2' (wz (res_of sw Fc cap q))
             a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' R' F fc m' mdv X' EGP ETP ES9 ES10 ES11 eq_refl FR FA MUW WM EF' GU'
             RO' (STF m' ph' ST' PH' HSV')).
    unfold psn_res. split; [exact MSx|]. split; [destruct (hdr_kind (kind sw Fc cap q)); exact HPSx|].
    split; [exists bjx; split; [exact HBJx|]; split; [rewrite LBx; exact HBN | exact FBx]|]. exact HTSx.
  - hide_hyp HTSe. rewrite (chain_empty sw Fc cap f q lh KE).
    pose proof (kind_empty sw Fc cap q KE) as K16. unfold flen in K16.
    assert (HTS2 : ts <> 0 -> spZ regs0 <= ts /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\ rw_cells rsegs m' ts [C8 tsv]).
    { intros T. destruct (HTS T) as (T1 & T2 & _). split; [exact T1|]. split; [exact T2 | exact (HTSe T)]. }
    eapply SRO_mono; [| intros c Hc; eapply psn_fin_pre; [exact MUW | exact WM | exact Hc]].
    exact (IH regs0 F0 md sw Fc cap ps buf ts h swz b lo fl lol lvt lvid pv nx tsv pad
             ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' (wz h) a4' a5' a6' a7' s2 s3' s4 s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6'
             F fc m' ms' (q + 16) lh bj ph' mdv ltac:(lia) EQ' E0 E1 E2 E4 E7 E8 eq_refl ESW EGP ETP ES9 ES10 ES11 Hsp
             PH' HSV' ST' LO HLO HPS0 HPSe HSW MSe HIH HHL HBL HN26 HCAP HB4K HBJe HBN HIB HBL2 HBH HBB HTS2 HTR
             EF' GU' RO' FR FA Hh Hl).
  - (* An oversized record: the `cap < incl` exit goes straight to the cap == 0 test (psn_after); no output. *)
    hide_hyp HTSb. pose proof (kind_big sw Fc cap q KB) as (K16 & KI & KC). unfold flen in K16, KC.
    pose proof (hw_range sw Fc q 8) as RI. change (hw sw Fc q 8) with (incl sw Fc q) in RI.
    eapply psn_evt_SRO; [exact EQ' | | exact Hh | exact Hl |].
    { eapply (psn_after HFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' ps buf cap h swz b q lo
                sw Fc pv nx lvt lvid bj ph' pad (getr regs0 2) (getr regs0 1) (getr regs0 8) (getr regs0 9)
                (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)
                (getr regs0 24)); try eassumption; try reflexivity; lia. }
    intros can3 ms3 POST3 EQ3.
    destruct POST3 as (ra3 & t03 & t13 & t23 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & s53 & s63 & t33 & t43
      & t53 & t63 & m3 & bj3 & DISJ3 & HPS3 & HBJ3 & HBN3 & MU3 & WM3 & RO3 & ST3 & PH3 & HSV3).
    destruct (psn_eg _ _ _ _ _ EF' GU' MU3 WM3 ltac:(unfold A_STDERR; disj_tac) ltac:(unfold A_GOT_GUARD; disj_tac)
                ltac:(unfold A_GUARD; disj_tac)) as [EF3 GU3].
    assert (HTS3 : ts <> 0 -> spZ regs0 <= ts /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\ rw_cells rsegs m3 ts [C8 tsv]).
    { intros T. destruct (HTS T) as (T1 & T2 & _). split; [exact T1|]. split; [exact T2|].
      exact (rw_cells_transport rsegs _ _ _ _ _ (HTSb T) MU3 WM3 ltac:(disj_tac)). }
    hide_hyp HTS3.
    assert (MU3W : munch (psn_W regs0 ps buf cap ts h) m' m3)
      by (clear - MU3 Hsp; eapply munch_weaken; [| exact MU3]; unfold sub_fp, psn_W, NEXT_K; out_tac).
    pose proof (munch_trans _ _ _ _ MUW MU3W) as MUW3.
    pose proof (wmono_trans rsegs _ _ _ WM WM3) as WM3'.
    destruct DISJ3 as [(K1 & -> & MS3) | (KN & -> & MS3)].
    + rewrite (chain_big sw Fc cap f q lh K1). cbn [fst snd].
      eapply SRO_mono; [| intros c Hc; eapply psn_fin_pre; [exact MUW3 | exact WM3' | exact Hc]].
      exact (IH regs0 F0 md sw Fc cap ps buf ts h swz b lo fl lol lvt lvid pv nx tsv pad
               ra3 sp gp tp t03 t13 t23 s0 s1 a03 a13 a23 (wz h) a43 a53 a63 a73 s2 (wz (-1)) s4 s53 s63 s7 s8 s9 s10 s11
               t33 t43 t53 t63 F fc m3 ms3 (q + 16 + incl sw Fc q) (Some q) bj3 ph' mdv ltac:(lia) EQ3 E0 E1 E2 E4 E7 E8
               eq_refl ESW EGP ETP ES9 ES10 ES11 Hsp PH3 HSV3 ST3 LO HLO HPS0 HPS3 HSW MS3 HIH HHL HBL HN26 HCAP HB4K
               HBJ3 HBN3 HIB HBL2 HBH HBB HTS3 HTR EF3 GU3 RO3 FR FA Hh Hl).
    + assert (KN' : kind sw Fc cap q = KBig0 \/ kind sw Fc cap q = KCutBig)
        by (destruct KC as [(_ & K)|[(_ & _ & K)|(_ & _ & K)]]; [left | exfalso; exact (KN K) | right]; exact K).
      rewrite (chain_nbig sw Fc cap f q lh KN'). cbn [fst snd].
      apply SRO_ret.
      destruct (@eqv_mkst (YK11.mkFP F fc) _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
      apply (psn_fin_exit regs0 F0 md m sw Fc cap ps buf ts h b swz lo fl lol lvt lvid pad pv nx tsv q (Some q)
               gp tp s9 s10 s11 t03 t13 t23 (wz (-1)) a13 a23 a33 a43 a53 a63 a73 t33 t43 t53 t63 R3 F fc m3 mdv X3 EGP ETP
               ES9 ES10 ES11 ltac:(unfold res_of; destruct KN' as [K|K]; rewrite K; reflexivity) FR FA MUW3 WM3' EF3 GU3
               RO3 (STF m3 ph' ST3 PH3 HSV3)).
      unfold psn_res, vt_of, vid_of, ts_of. destruct KN' as [K|K]; rewrite K; cbn [is_fit].
      all: split; [exact MS3|]; split; [exact HPS3|];
        split; [exists bj3; split; [exact HBJ3|]; split; [exact HBN3 | discriminate]|];
        intros T; exact (proj2 (proj2 (HTS3 T))).
Qed.

End K.
