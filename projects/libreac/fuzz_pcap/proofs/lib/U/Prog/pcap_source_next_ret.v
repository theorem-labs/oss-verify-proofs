From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fread_c fread_ro_c
  pcap_source_struct pcap_source_struct_next pcap_lib pcap_source_next_lib pcap_source_next_ep pcap_source_next_skip.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma kind_big : forall sw F cap q, big_kind (kind sw F cap q) = true ->
  16 <= flen F - q /\ cap < incl sw F q /\
  ((cap = 0 /\ kind sw F cap q = KBig0) \/
   (cap <> 0 /\ q + 16 + incl sw F q <= flen F /\ kind sw F cap q = KBig) \/
   (cap <> 0 /\ flen F < q + 16 + incl sw F q /\ kind sw F cap q = KCutBig)).
Proof.
  intros sw F cap q H. unfold big_kind in H. unfold kind in *.
  destruct (Z.eqb_spec (flen F - q) 0); [discriminate|].
  destruct (Z.ltb_spec (flen F - q) 16); [discriminate|].
  destruct (Z.eqb_spec (incl sw F q) 0); [discriminate|].
  destruct (Z.leb_spec (incl sw F q) cap);
    [destruct (Z.leb_spec (q + 16 + incl sw F q) (flen F)); discriminate|].
  destruct (Z.eqb_spec cap 0); [split; [lia|split; [lia|left; split; [assumption|reflexivity]]]|].
  destruct (Z.leb_spec (q + 16 + incl sw F q) (flen F)).
  - split; [lia|split; [lia|right; left; split; [assumption|split; [assumption|reflexivity]]]].
  - split; [lia|split; [lia|right; right; split; [assumption|split; [assumption|reflexivity]]]].
Qed.

Lemma kind_empty : forall sw F cap q, kind sw F cap q = KEmpty -> 16 <= flen F - q.
Proof.
  intros sw F cap q H. unfold kind in H.
  destruct (Z.eqb_spec (flen F - q) 0); [discriminate|].
  destruct (Z.ltb_spec (flen F - q) 16); [discriminate|]. lia.
Qed.

Lemma chain_exit : forall sw F cap f q lh, exit_kind (kind sw F cap q) = true ->
  chain sw F cap (S f) q lh = (q, [], if hdr_kind (kind sw F cap q) then Some q else lh).
Proof. intros sw F cap f q lh H. cbn [chain]. destruct (kind sw F cap q); try discriminate H; reflexivity. Qed.

Lemma chain_empty : forall sw F cap f q lh, kind sw F cap q = KEmpty ->
  chain sw F cap (S f) q lh = chain sw F cap f (q + 16) lh.
Proof. intros sw F cap f q lh K. cbn [chain]. rewrite K. reflexivity. Qed.

Lemma chain_nbig : forall sw F cap f q lh, kind sw F cap q = KBig0 \/ kind sw F cap q = KCutBig ->
  chain sw F cap (S f) q lh = (q, [], Some q).
Proof. intros sw F cap f q lh [K|K]; cbn [chain]; rewrite K; reflexivity. Qed.

Lemma chain_big : forall sw F cap f q lh, kind sw F cap q = KBig ->
  chain sw F cap (S f) q lh =
  (fst (fst (chain sw F cap f (q + 16 + incl sw F q) (Some q))),
   snd (fst (chain sw F cap f (q + 16 + incl sw F q) (Some q))),
   snd (chain sw F cap f (q + 16 + incl sw F q) (Some q))).
Proof.
  intros sw F cap f q lh K. cbn [chain]. rewrite K.
  destruct (chain sw F cap f (q + 16 + incl sw F q) (Some q)) as [[Q o] l]. reflexivity.
Qed.

Lemma psn_ret :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cap : Z),
    s7 = wz cap -> 0 <= cap < 2 ^ 64 ->
    evt rsegs
      (fun ms' =>
         (cap = 0 /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 (wz (-4)) s10 s8
                        t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x148)%Z)) fc None m (seg_rom rsegs)) \/
         (cap <> 0 /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 (wz (-4)) s10 s8
                        t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x108)%Z)) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0xf8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cap E7 HC.
  subst s7. unfold wz in *. do 4 step.
  destruct (Z.eq_dec cap 0) as [C|C].
  - subst cap. if_true. apply evt_done. left. split; reflexivity.
  - assert (EC : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
    if_false. apply evt_done. right. split; [exact C | reflexivity].
Qed.

Lemma psn_after : fread_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ps buf cap h swz b q lo : Z) (sw : bool) (Fc : list byte) (pv nx lvt lvid : word) (bj pad : list byte)
         (sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word),
    s1 = wz buf -> s2 = wz ps -> s3 = wz (bv_swrap 32 (incl sw Fc q)) -> s6 = wz (-1) -> s7 = wz cap ->
    s8 = wz (bv_unsigned sp + 12) -> s9 = wz (bv_unsigned sp + 16) ->
    big_kind (kind sw Fc cap q) = true ->
    bv_unsigned sp = bv_unsigned sp0 - 128 ->
    rw_cells rsegs m (bv_unsigned sp + 24)
      [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> (symaddr ImgPages.Ubsan.top) <= lo ->
    bv_unsigned sp0 <= ps -> rw_cells rsegs m ps (ps_cells (wz h) (wz swz) (wz (orig sw Fc q)) lvt lvid pad) ->
    mstl m h b Fc (q + 16) pv nx -> img_apart h 1304 -> h + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    0 <= cap < 2 ^ 64 -> 4096 <= buf -> u8arr rsegs m buf bj -> Z.of_nat (length bj) = Z.max cap 1 ->
    img_apart buf (Z.max cap 1) -> buf + Z.max cap 1 <= lo ->
    (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) -> (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length Fc) <= buf) ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' : word) m' bj',
         ((kind sw Fc cap q = KBig /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' (wz h) a4' a5' a6' a7'
                         s2 s3' s4' s5 s6 s7 (wz (bv_unsigned sp + 16)) (wz (-4)) s10 (wz (bv_unsigned sp + 12))
                         t3' t4' t5' t6')
                    F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x74)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (q + 16 + incl sw Fc q) pv nx) \/
          (kind sw Fc cap q <> KBig /\
           ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s0o s1o (wz (-1)) a1' a2' a3' a4' a5' a6' a7'
                         s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o t3' t4' t5' t6')
                    F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (pos_of sw Fc cap q) pv nx)) /\
         rw_cells rsegs m' ps (ps_cells (wz h) (wz swz) (wz (orig sw Fc q)) lvt lvid pad) /\
         u8arr rsegs m' buf bj' /\ Z.of_nat (length bj') = Z.max cap 1 /\
         munch [(bv_unsigned sp - 112, bv_unsigned sp); (buf, buf + Z.max cap 1); (h, h + 1304)] m m' /\
         wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (bv_unsigned sp + 24)
           [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0xf8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros HFR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ps buf cap h swz b q lo sw Fc pv nx lvt lvid bj pad sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o
    E1 E2 E3 E6 E7 E8 E9 KB Hsp HSV ST LO HLO HPS0 HPS HMS HIH HHL HBL HCAP HB4K HBJ HBN HIB HBL2 HBH HBB RO.
  subst s1 s2 s3 s6 s7 s8 s9.
  pose proof (zr_word sp0) as Rsp0. unfold inr64 in Rsp0.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs _ _ _ HPS) as HPR. cbn [cells_size csize ps_cells Nat.add] in HPR.
  pose proof (u8arr_len _ _ _ HBJ) as HBR.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (hw_range sw Fc q 8) as RI. change (hw sw Fc q 8) with (incl sw Fc q) in RI.
  destruct (kind_big sw Fc cap q KB) as (K16 & KI & KC). unfold flen in K16, KC.
  eapply evt_cut; [eapply psn_ret; [reflexivity | exact HCAP]|].
  intros ms' [(C0 & ->) | (C1 & ->)].
  - assert (K0 : kind sw Fc cap q = KBig0) by (destruct KC as [(_ & K)|[(C & _)|(C & _)]]; [exact K | lia | lia]).
    eapply evt_cut; [eapply psn_epi; [exact Hsp | exact HSV]|].
    intros ms'' ->. apply evt_done.
    do 18 eexists. exists m, bj.
    split; [right; split; [rewrite K0; discriminate|]; split; [reflexivity | unfold pos_of; rewrite K0; exact HMS]|].
    split; [exact HPS|]. split; [exact HBJ|]. split; [exact HBN|]. split; [apply munch_refl|].
    split; [apply wmono_refl|]. split; [exact RO|]. split; [exact ST | exact HSV].
  - unfold ps_cells in HPS.
    eapply evt_cut.
    { eapply (psn_skip HFR (Z.to_nat (incl sw Fc q)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                F fc m ps buf cap h b (q + 16) (incl sw Fc q) lo Fc pv nx (wz swz) (wz (orig sw Fc q)) lvt lvid bj pad);
        try reflexivity; try eassumption; lia. }
    intros ms'' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & t3' & t4' & t5' & t6'
      & m' & DISJ & HPS' & (bj' & HBJ' & LB') & MU & WM & RO' & ST').
    xp_rw HSV MU WM.
    destruct DISJ as [(FIT & -> & MS') | (CUT & -> & MS')].
    + assert (KK : kind sw Fc cap q = KBig) by (destruct KC as [(C & _)|[(_ & _ & K)|(_ & C & _)]]; [lia | exact K | lia]).
      apply evt_done.
      exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s3', s4', t3', t4', t5', t6', m', bj'.
      split; [left; split; [exact KK|]; split; [reflexivity | exact MS']|].
      split; [exact HPS'|]. split; [exact HBJ'|]. split; [rewrite LB'; exact HBN|]. split; [exact MU|].
      split; [exact WM|]. split; [exact RO'|]. split; [exact ST' | exact HSV].
    + assert (KK : kind sw Fc cap q = KCutBig)
        by (destruct KC as [(C & _)|[(_ & C & _)|(_ & _ & K)]]; [lia | lia | exact K]).
      eapply evt_cut; [eapply psn_epi; [exact Hsp | exact HSV]|].
      intros ms3 ->. apply evt_done.
      do 18 eexists. exists m', bj'.
      split; [right; split; [rewrite KK; discriminate|]; split; [reflexivity | unfold pos_of; rewrite KK; exact MS']|].
      split; [exact HPS'|]. split; [exact HBJ'|]. split; [rewrite LB'; exact HBN|]. split; [exact MU|].
      split; [exact WM|]. split; [exact RO'|]. split; [exact ST' | exact HSV].
  Unshelve. all: try exact (Z_to_bv 64 0).
Qed.
