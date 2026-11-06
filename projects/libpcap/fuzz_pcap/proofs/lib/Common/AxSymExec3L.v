(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk SymExec AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SymExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module AX2L.
Import AX2. Import AX2B. Import AX2F.

(* [comment removed for export] *)
Definition dsyn1 (bc : bctx) (c : saddr) (m : expr) (kb : expr) (lo hi : Z) : bool :=
  if (if expr_eqb kb (a_base c) then Z.leb (a_off c) lo else false) then
    match xloB bc m with Some ml => Z.leb hi (a_off c + ml) | None => false end
  else false.
Lemma dsyn_cons : forall bc c m r kb lo hi,
  AX2W.dsyn bc ((c, m) :: r) kb lo hi = (dsyn1 bc c m kb lo hi || AX2W.dsyn bc r kb lo hi)%bool.
Proof.
  intros bc c m r kb lo hi. cbn [AX2W.dsyn]. unfold dsyn1.
  destruct (if expr_eqb kb (a_base c) then Z.leb (a_off c) lo else false); [|reflexivity].
  destruct (xloB bc m) as [ml|]; [|reflexivity]. destruct (Z.leb hi (a_off c + ml)); reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint dsynH (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (kb : expr) (lo hi : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if dsyn1 bc c2 m2 kb lo hi then sub_itvB bc b1 k1 n1 c1 m1 else false) then true
      else if (if dsyn1 bc c1 m1 kb lo hi then sub_itvB bc b1 k1 n1 c2 m2 else false) then true
      else dsynH bc rest b1 k1 n1 kb lo hi
  | _ :: rest => dsynH bc rest b1 k1 n1 kb lo hi
  end.
Lemma dsynH_eq : forall bc kn b1 k1 n1 kb lo hi,
  AX2W.dsyn bc (disj_sidesB bc kn b1 k1 n1) kb lo hi = dsynH bc kn b1 k1 n1 kb lo hi.
Proof.
  intros bc kn b1 k1 n1 kb lo hi. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sidesB dsynH]; try exact IH.
  destruct (sub_itvB bc b1 k1 n1 c2 m2), (sub_itvB bc b1 k1 n1 c1 m1); rewrite ?dsyn_cons, ?IH;
    destruct (dsyn1 bc c1 m1 kb lo hi), (dsyn1 bc c2 m2 kb lo hi); reflexivity.
Qed.

Definition gnumR (rng : option (Z * Z)) (br2 : option (Z * Z)) (rk m1 glo ghi : Z) : bool :=
  match rng, br2 with
  | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + rk + m1 - lo2) glo || Z.leb ghi (lo1 + rk - hi2))%bool
  | _, _ => false
  end.
Definition gverdictH (bc : bctx) (rng : option (Z * Z)) (rb : expr) (rk m1 : Z) (x : lgx) (id : positive) : bool :=
  match pt_get (nt_info (lx_nt x)) id, pt_get (lx_hull x) id with
  | Some bi, Some (glo, ghi) => if gnumR rng (bi_br bi) rk m1 glo ghi then true else dsynH bc (bc_fk bc) rb rk m1 (bi_base bi) glo ghi
  | _, _ => false
  end.
Lemma gverdictH_eq : forall bc rb rk n x id,
  gverdictH bc (base_rangeB bc rb) rb rk (zlit64 (Z.of_nat n)) x id
  = gverdict bc (mk_lprep bc rb rk n) x rk (zlit64 (Z.of_nat n)) id.
Proof.
  intros bc rb rk n x id. unfold gverdictH, gverdict.
  destruct (pt_get (nt_info (lx_nt x)) id) as [bi|]; [|reflexivity].
  destruct (pt_get (lx_hull x) id) as [[glo ghi]|]; [|reflexivity].
  unfold gnumR, gnum, mk_lprep. cbn [sp_rng sp_D]. rewrite dsynH_eq. reflexivity.
Qed.

Fixpoint log_lookupH (bc : bctx) (rng : option (Z * Z)) (x : lgx) (memo : ptree bool) (log : list sentry) (ids : list positive)
         (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log, ids with
  | [], _ => LMiss acc hints
  | _ :: _, [] => log_lookupP bc (mk_lprep bc rb rk n) log rb rk n sx hints acc
  | SE (SA kb kk) w v :: rest, id :: ids' =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupH bc rng x memo rest ids' rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let '(gv, memo') := match pt_get memo id with
                              | Some b => (b, memo)
                              | None => let b := gverdictH bc rng rb rk (zlit64 (Z.of_nat n)) x id in (b, pt_set id b memo)
                              end in
          if (Nat.leb w 8 && gv)%bool then log_lookupH bc rng x memo' rest ids' rb rk n sx hints acc
          else log_lookupG bc (mk_lprep bc rb rk n) x memo' log ids rb rk n sx hints acc
      end
  end.

Lemma log_lookupH_eq : forall fk x log ids memo rb rk n sx hints acc,
  Nat.leb n 8 = true -> LXI (mkbc fk) x log ids ->
  MEMOG (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x rk (zlit64 (Z.of_nat n)) memo ->
  log_lookupH (mkbc fk) (base_rangeB (mkbc fk) rb) x memo log ids rb rk n sx hints acc
  = log_lookupP (mkbc fk) (mk_lprep (mkbc fk) rb rk n) log rb rk n sx hints acc.
Proof.
  intros fk x log. induction log as [|[[kb kk] w v] rest IH]; intros ids memo rb rk n sx hints acc Hn HL HM;
    [reflexivity|].
  pose proof HL as [HT HF].
  inversion HF as [|e0 id l0 ids' [HIn Hh] HF' E1 E2]; subst.
  cbn [log_lookupH log_lookupP].
  assert (HL' : LXI (mkbc fk) x rest ids') by (split; assumption).
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) eqn:Er; try reflexivity; [apply IH; assumption|].
  set (gv0 := gverdict (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x rk (zlit64 (Z.of_nat n)) id).
  assert (HGM : exists memo', (match pt_get memo id with
                               | Some b => (b, memo)
                               | None => (gverdictH (mkbc fk) (base_rangeB (mkbc fk) rb) rb rk (zlit64 (Z.of_nat n)) x id,
                                          pt_set id (gverdictH (mkbc fk) (base_rangeB (mkbc fk) rb) rb rk (zlit64 (Z.of_nat n)) x id) memo)
                               end) = (gv0, memo')
                 /\ MEMOG (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x rk (zlit64 (Z.of_nat n)) memo').
  { destruct (pt_get memo id) as [b|] eqn:Eb.
    - exists memo. rewrite (HM _ _ Eb). split; [reflexivity|exact HM].
    - exists (pt_set id gv0 memo). rewrite gverdictH_eq. split; [reflexivity|].
      intros id' b' Hb'. destruct (Pos.eq_dec id' id) as [->|Hne].
      + rewrite pt_gss in Hb'. injection Hb' as <-. reflexivity.
      + rewrite (pt_gso _ id' id _ memo Hne) in Hb'. exact (HM _ _ Hb'). }
  destruct HGM as (memo' & Egm & HM'). rewrite Egm. cbv beta iota.
  destruct (Nat.leb w 8 && gv0)%bool eqn:Hwg.
  - apply andb_prop in Hwg as [Hw Hgv].
    rewrite Hw. rewrite (gverdict_apart fk x kb kk w id rb rk n HT HIn Hh Hw Hn Hgv). apply IH; assumption.
  - rewrite (log_lookupG_eq fk x (SE (SA kb kk) w v :: rest) (id :: ids') memo' rb rk n sx hints acc Hn HL HM').
    cbn [log_lookupP]. rewrite Er. reflexivity.
Qed.
Definition sym_readBIH (segs : list Segment) (ss : sym_state) (x : lgx) (ids : list positive) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match (if Nat.leb n 8
         then log_lookupH bc (base_rangeB bc (a_base a)) x PTLeaf (s_log ss) ids (a_base a) (a_off a) n sx' (sc_hints scr) []
         else log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.


Lemma sym_readBIH_eq : forall fk segs ss x ids kx scr, LXI (mkbc fk) x (s_log ss) ids ->
  sym_readBIH segs ss x ids (mkbc fk) kx scr = sym_readBIP segs ss (mkbc fk) kx scr.
Proof.
  intros fk segs ss x ids kx scr HL. apply functional_extensionality. intros a.
  apply functional_extensionality. intros n. apply functional_extensionality. intros sx'.
  unfold sym_readBIH, sym_readBIP. destruct (Nat.leb n 8) eqn:Hn; [|reflexivity].
  rewrite (log_lookupH_eq fk x (s_log ss) ids PTLeaf (a_base a) (a_off a) n sx' (sc_hints scr) [] Hn HL); [reflexivity|].
  intros id b H. rewrite pt_get_leaf in H. discriminate.
Qed.

Definition sym_stepBIH (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (x : lgx) (ids : list positive) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBIH segs ss x ids bc kx scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIH segs ss x ids bc kx scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBIH segs ss x ids bc kx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.


Lemma sym_stepBIH_eq : forall fk kx segs i ss x ids scr, LXI (mkbc fk) x (s_log ss) ids ->
  sym_stepBIH (mkbc fk) kx segs i ss x ids scr = sym_stepBIP (mkbc fk) kx segs i ss scr.
Proof.
  intros fk kx segs i ss x ids scr HL. unfold sym_stepBIH, sym_stepBIP.
  rewrite (sym_readBIH_eq fk segs ss x ids kx scr HL). reflexivity.
Qed.


(* [comment removed for export] *)
Definition id_ok (bc : bctx) (rng : option (Z * Z)) (rb : expr) (rk : Z) (n : nat) (x : lgx) (p : positive) : bool :=
  match pt_get (nt_info (lx_nt x)) p with
  | Some bi =>
      if expr_eqb rb (bi_base bi) then
        match pt_get (lx_hull x) p with
        | Some (lo, hi) => (Z.leb hi rk || Z.leb (rk + Z.of_nat n) lo)%bool
        | None => true
        end
      else gverdictH bc rng rb rk (zlit64 (Z.of_nat n)) x p
  | None => true
  end.
Fixpoint all_pos (f : positive -> bool) (p : positive) (k : nat) : bool :=
  match k with O => true | S k' => (f p && all_pos f (Pos.succ p) k')%bool end.
Definition miss_fast (bc : bctx) (rng : option (Z * Z)) (x : lgx) (rb : expr) (rk : Z) (n : nat) : bool :=
  all_pos (id_ok bc rng rb rk n x) xH (Pos.to_nat (nt_next (lx_nt x))).
Lemma all_pos_ok : forall f k p q, all_pos f p k = true ->
  (Pos.to_nat p <= Pos.to_nat q < Pos.to_nat p + k)%nat -> f q = true.
Proof.
  intros f k. induction k as [|k IH]; intros p q H Hq; [lia|].
  cbn [all_pos] in H. apply andb_prop in H as [H1 H2].
  destruct (Nat.eq_dec (Pos.to_nat q) (Pos.to_nat p)) as [E|NE].
  - apply Pos2Nat.inj in E. subst q. exact H1.
  - apply (IH (Pos.succ p) q H2). rewrite Pos2Nat.inj_succ. lia.
Qed.
Lemma miss_fast_sound : forall fk x log ids rb rk n sx hints acc,
  (1 <= n <= 8)%nat -> LXI (mkbc fk) x log ids -> Forall (fun e => (e_width e <= 8)%nat) log ->
  miss_fast (mkbc fk) (base_rangeB (mkbc fk) rb) x rb rk n = true ->
  log_lookupP (mkbc fk) (mk_lprep (mkbc fk) rb rk n) log rb rk n sx hints acc = LMiss acc hints.
Proof.
  intros fk x log ids rb rk n sx hints acc Hn [HT HF] HW HM.
  assert (Hn8 : Nat.leb n 8 = true) by (apply Nat.leb_le; lia).
  induction HF as [|e id rest ids' [HIn Hh] HF IH]; [reflexivity|].
  inversion HW as [|e0 l0 He HW' E0]; subst.
  destruct e as [[kb kk] w v]. cbn [e_addr e_width a_base a_off] in *.
  destruct HT as [HA HU]. destruct (HA _ _ _ HIn) as (_ & Hinfo & Hlt).
  assert (Hid : id_ok (mkbc fk) (base_rangeB (mkbc fk) rb) rb rk n x id = true).
  { apply (all_pos_ok _ _ xH id HM). split; [pose proof (Pos2Nat.is_pos id); rewrite Pos2Nat.inj_1; lia|].
    rewrite Pos2Nat.inj_1. apply Pos2Nat.inj_lt in Hlt. lia. }
  unfold id_ok in Hid. rewrite Hinfo in Hid. cbn [bi_base] in Hid.
  cbn [log_lookupP]. unfold rel_lit.
  assert (Hw8 : Nat.leb w 8 = true) by (apply Nat.leb_le; lia).
  destruct (expr_eqb rb kb) eqn:Eb.
  - destruct Hh as (glo & ghi & Hg & H1 & H2). rewrite Hg in Hid.
    rewrite (AX2W.zlit64_nat8 w Hw8) in H2.
    apply Bool.orb_true_iff in Hid as [Hid|Hid]; apply Z.leb_le in Hid.
    + replace (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w))%bool with false
        by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
      replace (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + Z.of_nat w) rk)%bool with true
        by (symmetry; apply Bool.orb_true_iff; right; apply Z.leb_le; lia).
      apply IH; assumption.
    + replace (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w))%bool with false
        by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      replace (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + Z.of_nat w) rk)%bool with true
        by (symmetry; apply Bool.orb_true_iff; left; apply Z.leb_le; lia).
      apply IH; assumption.
  - rewrite Hw8. rewrite gverdictH_eq in Hid.
    rewrite (gverdict_apart fk x kb kk w id rb rk n (conj HA HU) HIn Hh Hw8 Hn8 Hid).
    apply IH; assumption.
Qed.

Definition wide_step (i : instr) (ss' : sym_state) (wide : bool) : bool :=
  if is_storeI i then match s_log ss' with e :: _ => (wide || Nat.ltb 8 (e_width e))%bool | [] => wide end else wide.
Definition WIDE (wide : bool) (log : list sentry) : Prop := wide = false -> Forall (fun e => (e_width e <= 8)%nat) log.

Definition sym_readBIS (segs : list Segment) (ss : sym_state) (x : lgx) (ids : list positive) (wide : bool) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match (if Nat.leb n 8
         then (if (negb wide && Nat.leb 1 n && miss_fast bc (base_rangeB bc (a_base a)) x (a_base a) (a_off a) n)%bool
               then LMiss [] (sc_hints scr)
               else log_lookupH bc (base_rangeB bc (a_base a)) x PTLeaf (s_log ss) ids (a_base a) (a_off a) n sx' (sc_hints scr) [])
         else log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.


Lemma sym_readBIS_eq : forall fk segs ss x ids wide kx scr, LXI (mkbc fk) x (s_log ss) ids -> WIDE wide (s_log ss) ->
  sym_readBIS segs ss x ids wide (mkbc fk) kx scr = sym_readBIP segs ss (mkbc fk) kx scr.
Proof.
  intros fk segs ss x ids wide kx scr HL HWd. apply functional_extensionality. intros a.
  apply functional_extensionality. intros n. apply functional_extensionality. intros sx'.
  unfold sym_readBIS, sym_readBIP. destruct (Nat.leb n 8) eqn:Hn; [|reflexivity].
  destruct (negb wide && Nat.leb 1 n && miss_fast (mkbc fk) (base_rangeB (mkbc fk) (a_base a)) x (a_base a) (a_off a) n)%bool eqn:Hf.
  - apply andb_prop in Hf as [Hf Hm]. apply andb_prop in Hf as [Hw H1].
    apply Bool.negb_true_iff in Hw. apply Nat.leb_le in H1. apply Nat.leb_le in Hn.
    rewrite (miss_fast_sound fk x (s_log ss) ids (a_base a) (a_off a) n sx' (sc_hints scr) [] ltac:(lia) HL (HWd Hw) Hm).
    reflexivity.
  - rewrite (log_lookupH_eq fk x (s_log ss) ids PTLeaf (a_base a) (a_off a) n sx' (sc_hints scr) [] Hn HL); [reflexivity|].
    intros id b H. rewrite pt_get_leaf in H. discriminate.
Qed.

Definition sym_stepBIS (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (x : lgx) (ids : list positive) (wide : bool) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBIS segs ss x ids wide bc kx scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIS segs ss x ids wide bc kx scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBIS segs ss x ids wide bc kx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.


Lemma sym_stepBIS_eq : forall fk kx segs i ss x ids wide scr, LXI (mkbc fk) x (s_log ss) ids -> WIDE wide (s_log ss) ->
  sym_stepBIS (mkbc fk) kx segs i ss x ids wide scr = sym_stepBIP (mkbc fk) kx segs i ss scr.
Proof.
  intros fk kx segs i ss x ids wide scr HL HWd. unfold sym_stepBIS, sym_stepBIP.
  rewrite (sym_readBIS_eq fk segs ss x ids wide kx scr HL HWd). reflexivity.
Qed.

Lemma wide_step_ok : forall bc kx segs i ss scr ss' scs scr' wide,
  sym_stepBIP bc kx segs i ss scr = SOk ss' scs scr' -> WIDE wide (s_log ss) -> WIDE (wide_step i ss' wide) (s_log ss').
Proof.
  intros bc kx segs i ss scr ss' scs scr' wide H HW. pose proof (sym_stepBIP_log _ _ _ _ _ _ _ _ _ H) as HG.
  unfold wide_step, WIDE in *. destruct (is_storeI i).
  - destruct HG as (e & He). rewrite He. intros Hz. apply Bool.orb_false_iff in Hz as [Hz1 Hz2].
    constructor; [apply Nat.ltb_ge in Hz2; exact Hz2 | exact (HW Hz1)].
  - rewrite HG. exact HW.
Qed.


(* [comment removed for export] *)
Fixpoint know_lookupA0B6 (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0B6 bc in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod two64)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod two64)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (l0 mod two64)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (l0 mod two64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erangeB bc len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.
Definition know_lookupA0I6 (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0B6 bc segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0B6 bc segs (kx_kn kx) rb rk n sx hints acc
  end.
Definition know_lookupABI6 (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0I6 bc kx segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Definition sym_readBIS6 (segs : list Segment) (ss : sym_state) (x : lgx) (ids : list positive) (wide : bool) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match (if Nat.leb n 8
         then (if (negb wide && Nat.leb 1 n && miss_fast bc (base_rangeB bc (a_base a)) x (a_base a) (a_off a) n)%bool
               then LMiss [] (sc_hints scr)
               else log_lookupH bc (base_rangeB bc (a_base a)) x PTLeaf (s_log ss) ids (a_base a) (a_off a) n sx' (sc_hints scr) [])
         else log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI6 bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.


Definition sym_stepBIS6 (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (x : lgx) (ids : list positive) (wide : bool) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit ((Z.shiftl (bv_signed imm) 12) mod two64)%Z) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit ((Z.shiftl (bv_signed imm) 12 + p) mod two64)%Z) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) ((p + bv_signed imm) mod two64)%Z) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (z mod two64 + bv_signed imm) (-2) mod two64)%Z) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := ((p + bv_signed imm) mod two64)%Z in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBIS6 segs ss x ids wide bc kx scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIS6 segs ss x ids wide bc kx scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBIS6 segs ss x ids wide bc kx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.


Lemma know_lookupA0B6_eq : know_lookupA0B6 = know_lookupA0B. Proof. reflexivity. Qed.
Lemma know_lookupABI6_eq : know_lookupABI6 = know_lookupABI. Proof. reflexivity. Qed.
Lemma sym_stepBIS6_eq : sym_stepBIS6 = sym_stepBIS. Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Fixpoint sym_execFH_go (t : itab) (bc : bctx) (kx : kix) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (x : lgx) (ids : list positive) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match itab_lookup t (s_pc ss) with
      | Some i =>
          match sym_stepBIH bc kx segs i ss x ids scr with
          | SOk ss' scs scr' =>
              let acc' := sc_add scs acc in
              let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
              sym_execFH_go t bc kx f false stops scr' ss' x' ids' acc'
                (if s_clean ss' then (ss', acc', scr') else ck)
          | SStop => if s_clean ss then (ss, acc, scr) else ck
          end
      | None =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_stepBIH bc kx segs i ss x ids scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
                  sym_execFH_go t bc kx f false stops scr' ss' x' ids' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
      end
  end.


#[using="Type"] Lemma sym_execFH_go_eq : forall t kx fuel fk first stops scr ss x ids acc ck, LXI (mkbc fk) x (s_log ss) ids ->
  sym_execFH_go t (mkbc fk) kx fuel first stops scr ss x ids acc ck = AX2F.sym_execFT_go segs t (mkbc fk) kx fuel first stops scr ss acc ck.
Proof.
  intros t kx fuel. induction fuel as [|f IH]; intros fk first stops scr ss x ids acc ck HL;
    cbn [sym_execFH_go sym_execFT_go]; [reflexivity|].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|].
  - rewrite (sym_stepBIH_eq fk kx segs i ss x ids scr HL).
    destruct (sym_stepBIP (mkbc fk) kx segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    pose proof (lx_step_ok _ _ _ _ _ _ _ _ _ x ids HL Hs) as HL'.
    destruct (lx_step (mkbc fk) i (SOk ss' scs scr') x ids) as [x' ids']. apply IH. exact HL'.
  - destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|reflexivity].
    destruct (is_ecall w); [reflexivity|].
    destruct (decode_any w) as [[i sz]|]; [|reflexivity].
    destruct (negb (Z.eqb sz 4)); [reflexivity|].
    rewrite (sym_stepBIH_eq fk kx segs i ss x ids scr HL).
    destruct (sym_stepBIP (mkbc fk) kx segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    pose proof (lx_step_ok _ _ _ _ _ _ _ _ _ x ids HL Hs) as HL'.
    destruct (lx_step (mkbc fk) i (SOk ss' scs scr') x ids) as [x' ids']. apply IH. exact HL'.
Qed.

Definition sym_execFH (t : itab) (kn : list kentry) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  let bc := mkbc (facts_of kn) in
  let '(x, ids) := lx_of_log bc (s_log (clr ss)) in
  sym_execFH_go t bc (mk_kix kn) fuel first stops scr (clr ss) x ids acc (clr ss, acc, scr).

#[using="Type"] Lemma sym_exec_viaFH : forall t kn fuel first stops scr ss acc r,
  itab_sound segs t -> s_know ss = kn ->
  sym_execFH t kn fuel first stops scr ss acc = r ->
  sym_exec segs fuel first stops scr ss acc = r.
Proof.
  intros t kn fuel first stops scr ss acc r Ht Hk H. rewrite <- H. unfold sym_execFH, sym_exec.
  pose proof (lx_of_log_ok (mkbc (facts_of kn)) (s_log (clr ss))) as HL.
  destruct (lx_of_log (mkbc (facts_of kn)) (s_log (clr ss))) as [x ids].
  rewrite (sym_execFH_go_eq t (mk_kix kn) fuel (facts_of kn) first stops scr (clr ss) x ids acc (clr ss, acc, scr) HL).
  symmetry. apply (AX2F.sym_execFT_go_eq segs t Ht). exact Hk.
Qed.

Fixpoint sym_execFS_go (t : itab) (bc : bctx) (kx : kix) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (x : lgx) (ids : list positive) (wide : bool) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match itab_lookup t (s_pc ss) with
      | Some i =>
          match sym_stepBIS bc kx segs i ss x ids wide scr with
          | SOk ss' scs scr' =>
              let acc' := sc_add scs acc in
              let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
              let wide' := wide_step i ss' wide in
              sym_execFS_go t bc kx f false stops scr' ss' x' ids' wide' acc'
                (if s_clean ss' then (ss', acc', scr') else ck)
          | SStop => if s_clean ss then (ss, acc, scr) else ck
          end
      | None =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_stepBIS bc kx segs i ss x ids wide scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
              let wide' := wide_step i ss' wide in
                  sym_execFS_go t bc kx f false stops scr' ss' x' ids' wide' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
      end
  end.


#[using="Type"] Lemma sym_execFS_go_eq : forall t kx fuel fk first stops scr ss x ids wide acc ck,
  LXI (mkbc fk) x (s_log ss) ids -> WIDE wide (s_log ss) ->
  sym_execFS_go t (mkbc fk) kx fuel first stops scr ss x ids wide acc ck = AX2F.sym_execFT_go segs t (mkbc fk) kx fuel first stops scr ss acc ck.
Proof.
  intros t kx fuel. induction fuel as [|f IH]; intros fk first stops scr ss x ids wide acc ck HL HWd;
    cbn [sym_execFS_go sym_execFT_go]; [reflexivity|].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|].
  - rewrite (sym_stepBIS_eq fk kx segs i ss x ids wide scr HL HWd).
    destruct (sym_stepBIP (mkbc fk) kx segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    pose proof (lx_step_ok _ _ _ _ _ _ _ _ _ x ids HL Hs) as HL'.
    pose proof (wide_step_ok _ _ _ _ _ _ _ _ _ wide Hs HWd) as HW'.
    destruct (lx_step (mkbc fk) i (SOk ss' scs scr') x ids) as [x' ids']. apply IH; assumption.
  - destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|reflexivity].
    destruct (is_ecall w); [reflexivity|].
    destruct (decode_any w) as [[i sz]|]; [|reflexivity].
    destruct (negb (Z.eqb sz 4)); [reflexivity|].
    rewrite (sym_stepBIS_eq fk kx segs i ss x ids wide scr HL HWd).
    destruct (sym_stepBIP (mkbc fk) kx segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    pose proof (lx_step_ok _ _ _ _ _ _ _ _ _ x ids HL Hs) as HL'.
    pose proof (wide_step_ok _ _ _ _ _ _ _ _ _ wide Hs HWd) as HW'.
    destruct (lx_step (mkbc fk) i (SOk ss' scs scr') x ids) as [x' ids']. apply IH; assumption.
Qed.

Definition sym_execFS (t : itab) (kn : list kentry) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  let bc := mkbc (facts_of kn) in
  let '(x, ids) := lx_of_log bc (s_log (clr ss)) in
  sym_execFS_go t bc (mk_kix kn) fuel first stops scr (clr ss) x ids (existsb (fun e => Nat.ltb 8 (e_width e)) (s_log (clr ss))) acc (clr ss, acc, scr).

#[using="Type"] Lemma sym_exec_viaFS : forall t kn fuel first stops scr ss acc r,
  itab_sound segs t -> s_know ss = kn ->
  sym_execFS t kn fuel first stops scr ss acc = r ->
  sym_exec segs fuel first stops scr ss acc = r.
Proof.
  intros t kn fuel first stops scr ss acc r Ht Hk H. rewrite <- H. unfold sym_execFS, sym_exec.
  pose proof (lx_of_log_ok (mkbc (facts_of kn)) (s_log (clr ss))) as HL.
  destruct (lx_of_log (mkbc (facts_of kn)) (s_log (clr ss))) as [x ids].
  assert (HW : WIDE (existsb (fun e => Nat.ltb 8 (e_width e)) (s_log (clr ss))) (s_log (clr ss))).
  { intros Hz. apply Forall_forall. intros e He. destruct (Nat.ltb 8 (e_width e)) eqn:E.
    - exfalso. assert (existsb (fun e => Nat.ltb 8 (e_width e)) (s_log (clr ss)) = true) by (apply existsb_exists; exists e; auto).
      congruence.
    - apply Nat.ltb_ge in E. exact E. }
  rewrite (sym_execFS_go_eq t (mk_kix kn) fuel (facts_of kn) first stops scr (clr ss) x ids _ acc (clr ss, acc, scr) HL HW).
  symmetry. apply (AX2F.sym_execFT_go_eq segs t Ht). exact Hk.
Qed.

Fixpoint sym_execFS6_go (t : itab) (bc : bctx) (kx : kix) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (x : lgx) (ids : list positive) (wide : bool) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match itab_lookup t (s_pc ss) with
      | Some i =>
          match sym_stepBIS6 bc kx segs i ss x ids wide scr with
          | SOk ss' scs scr' =>
              let acc' := sc_add scs acc in
              let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
              let wide' := wide_step i ss' wide in
              sym_execFS6_go t bc kx f false stops scr' ss' x' ids' wide' acc'
                (if s_clean ss' then (ss', acc', scr') else ck)
          | SStop => if s_clean ss then (ss, acc, scr) else ck
          end
      | None =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_stepBIS6 bc kx segs i ss x ids wide scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
              let wide' := wide_step i ss' wide in
                  sym_execFS6_go t bc kx f false stops scr' ss' x' ids' wide' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
      end
  end.


Lemma sym_execFS6_go_eq : sym_execFS6_go = sym_execFS_go.
Proof. reflexivity. Qed.
Definition sym_execFS6 (t : itab) (kn : list kentry) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  let bc := mkbc (facts_of kn) in
  let '(x, ids) := lx_of_log bc (s_log (clr ss)) in
  sym_execFS6_go t bc (mk_kix kn) fuel first stops scr (clr ss) x ids (existsb (fun e => Nat.ltb 8 (e_width e)) (s_log (clr ss))) acc (clr ss, acc, scr).
#[using="Type"] Lemma sym_exec_viaFS6 : forall t kn fuel first stops scr ss acc r,
  itab_sound segs t -> s_know ss = kn ->
  sym_execFS6 t kn fuel first stops scr ss acc = r ->
  sym_exec segs fuel first stops scr ss acc = r.
Proof.
  intros t kn fuel first stops scr ss acc r Ht Hk H. apply (sym_exec_viaFS t kn fuel first stops scr ss acc r Ht Hk).
  rewrite <- H. unfold sym_execFS6, sym_execFS. rewrite sym_execFS6_go_eq. reflexivity.
Qed.

End WithSegs.


(* [comment removed for export] *)
Section Carry2.
Import AX2W.
Definition is_factK (K : kentry) : bool :=
  match K with KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true | _ => false end.
Lemma chainKN_fact : forall bc sxs K, is_factK K = true -> chainKN bc sxs K = [K].
Proof.
  intros bc sxs K HK. induction sxs as [|sx rest IH]; [reflexivity|].
  destruct K; try discriminate; cbn [chainKN prune1pcK]; exact IH.
Qed.
Fixpoint entriesZ2 (bc : bctx) (sxs : list stx) (gl glz : glW) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match K with
           | KWord _ w _ =>
               if Nat.leb w 8 then
                 match pt_get gl (ei_gid ei) with
                 | Some (g, kb, fl) =>
                     if (if inb g ei then expr_eqb kb (ei_kb ei) else false)
                     then chainKF bc fl K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                     else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 end
               else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
           | _ =>
               match zdesc K with
               | Some (kk, m) =>
                   match pt_get glz (ei_bid ei) with
                   | Some (g, kb, fl) =>
                       if (if inb g (EI (ei_bid ei) xH (ei_kb ei) (ei_br ei) kk (Some m)) then expr_eqb kb (ei_kb ei) else false)
                       then chainKF bc fl K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                       else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                   | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                   end
               | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
               end
           end
       | None => if is_factK K then [K] else chainKN bc sxs K
       end) ++ entriesZ2 bc sxs gl glz rest irest
  | _, _ => []
  end.

Lemma entriesZ2_eq : forall bc sxs gl glz kn infos, entriesZ2 bc sxs gl glz kn infos = entriesZ bc sxs gl glz kn infos.
Proof.
  intros bc sxs gl glz kn. induction kn as [|K rest IH]; intros infos; [reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|].
  cbn [entriesZ2 entriesZ]. rewrite IH. f_equal.
  destruct oi as [ei|]; [reflexivity|].
  destruct (is_factK K) eqn:E; [rewrite (chainKN_fact bc sxs K E)|]; reflexivity.
Qed.
Definition carryWZ2 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsM bc log nt_empty in
  let '(r, gs) := scanW bc kn t0 gsw_empty in
  let '(infos, _) := r in
  let '(ogs, gss) := scan_stores sxs gsw_empty in
  fst (stores_partW bc sxs ogs (tbl_init (gw_bnds gss)))
    ++ entriesZ2 bc sxs (mk_glW bc (gw_bnds gs) sxs) (mk_glZ bc (zhulls kn infos PTLeaf) sxs) kn infos.

Lemma carryWZ2_eq : forall bc log kn, carryWZ2 bc log kn = carryWZ bc log kn.
Proof.
  intros bc log kn. unfold carryWZ2, carryWZ.
  destruct (mk_stxsM bc log nt_empty) as [sxs t0].
  destruct (scanW bc kn t0 gsw_empty) as [[infos t1] gs].
  destruct (scan_stores sxs gsw_empty) as [ogs gss].
  rewrite entriesZ2_eq. reflexivity.
Qed.
Definition carryWZK2 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryWZ2 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryWZK2_eq : forall bc log kn hints, carryWZK2 bc log kn hints = carryWZK bc log kn hints.
Proof.
  intros bc log kn hints. unfold carryWZK2, carryWZK.
  destruct log as [|s older]; [reflexivity|]. destruct hints as [|h hs]; [|reflexivity].
  rewrite carryWZ2_eq. reflexivity.
Qed.
End Carry2.
Definition carryF2 (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  carryWZK2 (mkbc (facts_of kn)) log kn hints.
Lemma carry_viaF2 : forall log kn hints r, carryF2 log kn hints = r -> carry log kn hints = r.
Proof.
  intros log kn hints r H. rewrite <- AX2W.carryWZK_eq. rewrite <- carryWZK2_eq. exact H.
Qed.


(* [comment removed for export] *)
Section CarryImg.
Import AX2W.
Definition is_imgK (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.
Fixpoint hullK_go (kn : list kentry) (acc : option (Z * Z)) : option (Z * Z) :=
  match kn with
  | [] => acc
  | KImg lo hi :: rest =>
      if Z.leb lo hi then
        hullK_go rest (match acc with Some (a, b) => Some (Z.min a lo, Z.max b hi) | None => Some (lo, hi) end)
      else hullK_go rest acc
  | _ :: rest => hullK_go rest acc
  end.
Definition hullK (kn : list kentry) : option (Z * Z) := hullK_go kn None.
Definition side_in (bc : bctx) (D : list (saddr * expr)) (lo hi : Z) : bool :=
  existsb (fun cm => let '(c, m) := cm in
                     (expr_eqb (ELit 0) (a_base c) && Z.leb (a_off c) lo &&
                      match xloB bc m with Some ml => Z.leb hi (a_off c + ml) | None => false end)%bool) D.
Definition img_skipH (bc : bctx) (sx : stx) (glo ghi : Z) : bool :=
  match a_base (sx_a sx) with
  | ELit 0 => false
  | _ =>
      (Z.ltb (ghi - glo) (2 ^ 64) &&
       ((match sp_rng (sx_sp sx) with
         | Some (lo1, hi1) => (Z.leb (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx))) glo || Z.leb ghi (lo1 + a_off (sx_a sx)))
         | None => false
         end)
        || side_in bc (sp_D (sx_sp sx)) glo ghi))%bool
  end.
Definition img_filter (bc : bctx) (h : option (Z * Z)) (sxs : list stx) : list stx :=
  match h with Some (glo, ghi) => List.filter (fun sx => negb (img_skipH bc sx glo ghi)) sxs | None => sxs end.

Lemma in_sidesB_ex : forall bc D b k n c m, In (c, m) D -> sub_itvB bc b k n c m = true -> in_sidesB bc D b k n = true.
Proof.
  intros bc D b k n c m. induction D as [|[c' m'] r IH]; intros HIn Hs; [destruct HIn|].
  cbn [in_sidesB]. destruct HIn as [E|HIn].
  - injection E as -> ->. rewrite Hs. reflexivity.
  - destruct (sub_itvB bc b k n c' m'); [reflexivity|]. exact (IH HIn Hs).
Qed.

Definition img_cond (bc : bctx) (sx : stx) (glo ghi : Z) : bool :=
  ((match sp_rng (sx_sp sx) with
    | Some (lo1, hi1) => (Z.leb (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx))) glo || Z.leb ghi (lo1 + a_off (sx_a sx)))
    | None => false
    end)
   || side_in bc (sp_D (sx_sp sx)) glo ghi)%bool.
Lemma img_skipH_split : forall bc sx glo ghi, img_skipH bc sx glo ghi = true ->
  a_base (sx_a sx) <> ELit 0 /\ (ghi - glo < 2 ^ 64)%Z /\ img_cond bc sx glo ghi = true.
Proof.
  intros bc sx glo ghi H. unfold img_skipH in H. unfold img_cond.
  destruct (a_base (sx_a sx)) as [[|p|p]| | | | | | |];
    try discriminate H;
    (apply andb_prop in H as [Hl Hc]; apply Z.ltb_lt in Hl; split; [discriminate|split; assumption]).
Qed.
Lemma prune1pcK_img_nz : forall bc sp wa w wv lo hi, a_base wa <> ELit 0 ->
  prune1pcK bc sp wa w wv (KImg lo hi) false None =
  if Z.ltb (hi - lo) (2 ^ 64) then (if ranges_apart_pB bc sp (a_base wa) (a_off wa) (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl []) else PRepl [].
Proof.
  intros bc sp wa w wv lo hi H. unfold prune1pcK.
  destruct (a_base wa) as [[|p|p]| | | | | | |]; try reflexivity. exfalso. apply H. reflexivity.
Qed.
Lemma img_apart : forall bc sx glo ghi lo hi,
  img_cond bc sx glo ghi = true -> (glo <= lo)%Z -> (lo <= hi)%Z -> (hi <= ghi)%Z -> (ghi - glo < 2 ^ 64)%Z ->
  ranges_apart_pB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) (ELit 0) lo (ELit (hi - lo)) = true.
Proof.
  intros bc sx glo ghi lo hi Hc H1 H2 H3 H4.
  assert (Hz : zlit64 (hi - lo) = (hi - lo)%Z).
  { unfold zlit64, two64. replace (Z.leb 0 (hi - lo) && Z.ltb (hi - lo) (2 ^ 64))%bool with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  unfold ranges_apart_pB, elen. cbv zeta. rewrite Hz.
  assert (Hb0 : base_rangeB bc (ELit 0) = Some (0, 0)%Z) by reflexivity. rewrite Hb0.
  unfold img_cond in Hc. apply Bool.orb_true_iff in Hc as [Hn|Hd].
  - destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate].
    replace ((hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx)) <=? 0 + lo)%Z
             || (0 + lo + (hi - lo) <=? lo1 + a_off (sx_a sx))%Z)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff in Hn as [Hn|Hn]; apply Z.leb_le in Hn; apply Bool.orb_true_iff;
      [left|right]; apply Z.leb_le; lia.
  - unfold side_in in Hd. apply existsb_exists in Hd as ([c m] & HIn & Hcm).
    apply andb_prop in Hcm as [Hcm Hm]. apply andb_prop in Hcm as [He Hlo]. apply Z.leb_le in Hlo.
    destruct (xloB bc m) as [ml|] eqn:Em; [|discriminate]. apply Z.leb_le in Hm.
    assert (HS : sub_itvB bc (ELit 0) lo (hi - lo) c m = true).
    { unfold sub_itvB. rewrite He, Em. cbn [andb].
      replace (a_off c <=? lo)%Z with true by (symmetry; apply Z.leb_le; lia).
      replace (lo + (hi - lo) <=? a_off c + ml)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    rewrite (in_sidesB_ex bc _ (ELit 0) lo (hi - lo) c m HIn HS).
    match goal with |- (if ?x then true else true) = true => destruct x; reflexivity end.
Qed.
Lemma img_skipH_keep : forall bc sx glo ghi lo hi,
  img_skipH bc sx glo ghi = true -> (glo <= lo)%Z -> (lo <= hi)%Z -> (hi <= ghi)%Z ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) (KImg lo hi) false None = PKeep.
Proof.
  intros bc sx glo ghi lo hi Hs H1 H2 H3. destruct (img_skipH_split bc sx glo ghi Hs) as (Hnz & H4 & Hc).
  rewrite (prune1pcK_img_nz _ _ _ _ _ lo hi Hnz).
  replace (Z.ltb (hi - lo) (2 ^ 64)) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite (img_apart bc sx glo ghi lo hi Hc H1 H2 H3 H4). reflexivity.
Qed.

Lemma prune1pcK_img_pieces : forall bc sp wa w wv lo hi same br2 l,
  prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PRepl l ->
  Forall (fun K' => exists lo' hi', K' = KImg lo' hi' /\ (lo <= lo')%Z /\ (lo' <= hi')%Z /\ (hi' <= hi)%Z) l.
Proof.
  intros bc sp wa w wv lo hi same br2 l H. unfold prune1pcK in H. cbv zeta in H.
  destruct (a_base wa) as [[|p|p]| | | | | | |].
  2-10: (destruct (Z.ltb (hi - lo) (2 ^ 64)); [destruct (ranges_apart_pB _ _ _ _ _ _ _ _)|]; try discriminate H;
         injection H as <-; constructor).
  injection H as <-. apply Forall_app. split.
  - destruct (Z.ltb lo (Z.min (a_off wa) hi)) eqn:E; constructor; [|constructor].
    apply Z.ltb_lt in E. exists lo, (Z.min (a_off wa) hi). split; [reflexivity|]. lia.
  - destruct (Z.ltb (Z.max lo (a_off wa + Z.of_nat w)) hi) eqn:E; constructor; [|constructor].
    apply Z.ltb_lt in E. exists (Z.max lo (a_off wa + Z.of_nat w)), hi. split; [reflexivity|]. lia.
Qed.

Lemma chainKN_img_filter : forall bc glo ghi sxs lo hi,
  (glo <= lo)%Z -> (lo <= hi)%Z -> (hi <= ghi)%Z ->
  chainKN bc (List.filter (fun sx => negb (img_skipH bc sx glo ghi)) sxs) (KImg lo hi) = chainKN bc sxs (KImg lo hi).
Proof.
  intros bc glo ghi sxs. induction sxs as [|sx rest IH]; intros lo hi H1 H2 H3; [reflexivity|].
  cbn [List.filter]. destruct (img_skipH bc sx glo ghi) eqn:Hs; cbn [negb].
  - cbn [chainKN]. rewrite (img_skipH_keep bc sx glo ghi lo hi Hs H1 H2 H3). apply IH; assumption.
  - cbn [chainKN]. destruct (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) (KImg lo hi) false None) as [|l] eqn:Hp.
    + apply IH; assumption.
    + pose proof (prune1pcK_img_pieces _ _ _ _ _ _ _ _ _ _ Hp) as HF.
      clear Hp. induction HF as [|K' l' (lo' & hi' & -> & A1 & A2 & A3) HF IHF]; [reflexivity|].
      cbn [flat_map kbase]. rewrite IHF. f_equal. apply IH; lia.
Qed.
Fixpoint entriesZ3 (bc : bctx) (sxs sxsI : list stx) (glo ghi : Z) (gl glz : glW) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match K with
           | KWord _ w _ =>
               if Nat.leb w 8 then
                 match pt_get gl (ei_gid ei) with
                 | Some (g, kb, fl) =>
                     if (if inb g ei then expr_eqb kb (ei_kb ei) else false)
                     then chainKF bc fl K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                     else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 end
               else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
           | _ =>
               match zdesc K with
               | Some (kk, m) =>
                   match pt_get glz (ei_bid ei) with
                   | Some (g, kb, fl) =>
                       if (if inb g (EI (ei_bid ei) xH (ei_kb ei) (ei_br ei) kk (Some m)) then expr_eqb kb (ei_kb ei) else false)
                       then chainKF bc fl K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                       else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                   | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                   end
               | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
               end
           end
       | None => if is_factK K then [K] else
                 match K with
                 | KImg lo hi => if (Z.leb glo lo && Z.leb lo hi && Z.leb hi ghi)%bool then chainKN bc sxsI K else chainKN bc sxs K
                 | _ => chainKN bc sxs K
                 end
       end) ++ entriesZ3 bc sxs sxsI glo ghi gl glz rest irest
  | _, _ => []
  end.

Lemma entriesZ3_eq : forall bc sxs glo ghi gl glz kn infos,
  entriesZ3 bc sxs (List.filter (fun sx => negb (img_skipH bc sx glo ghi)) sxs) glo ghi gl glz kn infos
  = entriesZ2 bc sxs gl glz kn infos.
Proof.
  intros bc sxs glo ghi gl glz kn. induction kn as [|K rest IH]; intros infos; [reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|].
  cbn [entriesZ3 entriesZ2]. rewrite IH. f_equal.
  destruct oi as [ei|]; [reflexivity|].
  destruct (is_factK K); [reflexivity|].
  destruct K; try reflexivity.
  destruct (Z.leb glo lo && Z.leb lo hi && Z.leb hi ghi)%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2, E3.
  apply chainKN_img_filter; assumption.
Qed.
Definition carryWZ3 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsM bc log nt_empty in
  let '(r, gs) := scanW bc kn t0 gsw_empty in
  let '(infos, _) := r in
  let '(ogs, gss) := scan_stores sxs gsw_empty in
  fst (stores_partW bc sxs ogs (tbl_init (gw_bnds gss)))
    ++ match hullK kn with
       | Some (glo, ghi) => entriesZ3 bc sxs (List.filter (fun sx => negb (img_skipH bc sx glo ghi)) sxs) glo ghi
                              (mk_glW bc (gw_bnds gs) sxs) (mk_glZ bc (zhulls kn infos PTLeaf) sxs) kn infos
       | None => entriesZ2 bc sxs (mk_glW bc (gw_bnds gs) sxs) (mk_glZ bc (zhulls kn infos PTLeaf) sxs) kn infos
       end.

Lemma carryWZ3_eq : forall bc log kn, carryWZ3 bc log kn = carryWZ2 bc log kn.
Proof.
  intros bc log kn. unfold carryWZ3, carryWZ2.
  destruct (mk_stxsM bc log nt_empty) as [sxs t0].
  destruct (scanW bc kn t0 gsw_empty) as [[infos t1] gs].
  destruct (scan_stores sxs gsw_empty) as [ogs gss].
  destruct (hullK kn) as [[glo ghi]|]; [rewrite entriesZ3_eq|]; reflexivity.
Qed.
Definition carryWZK3 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryWZ3 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryWZK3_eq : forall bc log kn hints, carryWZK3 bc log kn hints = carryWZK bc log kn hints.
Proof.
  intros bc log kn hints. rewrite <- carryWZK2_eq. unfold carryWZK3, carryWZK2.
  destruct log as [|s older]; [reflexivity|]. destruct hints as [|h hs]; [|reflexivity].
  rewrite carryWZ3_eq. reflexivity.
Qed.
End CarryImg.
Definition carryF3 (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  carryWZK3 (mkbc (facts_of kn)) log kn hints.
Lemma carry_viaF3 : forall log kn hints r, carryF3 log kn hints = r -> carry log kn hints = r.
Proof.
  intros log kn hints r H. rewrite <- AX2W.carryWZK_eq. rewrite <- carryWZK3_eq. exact H.
Qed.

End AX2L.
