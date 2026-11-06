(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3 XAxSymExec3B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list04bool03nat37Corelib4Init5Logici92eq37Corelib7Numbers7BinNumsk21Z3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelf7Segment99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XAxFast3AXF3FPX~~~~~~peeknow_lookupA0F89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~v44exprv46kentryv44lresv48sidecond89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B~~~~~~hlb4bctxhlbeknow_lookupA0Bhlb3kixhlb5kx_kn03nilhlb9kx_select06optionv44LHitpefknow_lookupA0IFv45LMissv46LStuckv4eknow_bytes_litv4clit_of_bytes3h5LinuxProcessSemantics5Riscv5Instrij05instrv47scriptsv47stepresv49sym_statev45SStopv46s_nexta9OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XAxFast3AXF3FPX8WithSegs~~~~~~ioebsym_stepBIFv43SOkv46cap_rdhlb9x_filterB46Stdlib5Arith8PeanoNat3Natjg73lebv44itabv43clrioeh0sym_execTXBIF_gohlbeknow_lookupA0Ipefknow_lookupABIFhlbeknow_lookupABIhlbasym_stepBIioecsym_stepXBIFhlbbsym_stepXBIhlbfsym_execTXBI_goioedsym_execTXBIFhlbcsym_execTXBI" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module AXF.
Import AX2. Import AX2B.
Section FPX. Context {fx : XPropExec.FPState}.

(* [comment removed for export] *)
Fixpoint know_lookupA0F (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0F bc in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>   (* [comment removed for export] *)
          if expr_eqb rb kb then
            if Z.leb kk rk then
              if Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w) then LHit (mkExt sx (Z.to_nat (rk - kk)) n v) acc hints
              else know_lookup segs rest rb rk n sx hints acc
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with
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
              match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with
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
                  if Z.leb (rk + Z.of_nat n) (kk + (zmod64 l0))
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (zmod64 l0)) rk then know_lookup segs rest rb rk n sx hints acc
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

(* [comment removed for export] *)
Lemma know_lookupA0F_eqf : ltac2:(zQ "d0!h8!he!i4!jd!lb!p4!u3!hj9!hk0!hk9!hl0!hq2!hqa>2bc$b>4segs@1$0$5>2kn@1$0$8@3$3>2rb$7>2rk$4>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$a$9@3$6^3^2^1@3$c^3^2^1").
Proof.
  intros bc segs kn. induction kn as [|K rest IH];
    apply functional_extensionality; intros rb; apply functional_extensionality; intros rk;
    apply functional_extensionality; intros n; apply functional_extensionality; intros sx;
    apply functional_extensionality; intros hints; apply functional_extensionality; intros acc; [reflexivity|].
  cbn [know_lookupA0F know_lookupA0B]. rewrite IH.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try reflexivity; try (destruct len; rewrite ?zmod64_eq; reflexivity).
  (* [comment removed for export] *)
  unfold rel_lit. destruct (expr_eqb rb kb); [|reflexivity].
  destruct (Z.leb kk rk), (Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w)); cbn [andb];
    try reflexivity; destruct (_ || _)%bool; reflexivity.
Qed.
Lemma know_lookupA0F_eq : ltac2:(zQ "d0!h8!he!i4!jd!lb!p4!u3!hj9!hk0!hk9!hl0!hq2!hqa>2bc$b>4segs@1$0$5>2kn@1$0$8>2rb$7>2rk$4>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$a@3$3$9@9$6^9^8^7^6^5^4^3^2^1@9$c^9^8^7^6^5^4^3^2^1").
Proof. intros. rewrite know_lookupA0F_eqf. reflexivity. Qed.

(* [comment removed for export] *)
Definition know_lookupA0IF : ltac2:(zQ "a0!h8!he!i4!lb!p4!hj9!hk9!hl0!hq2!hrc>2bc$8>2kx$9>4segs@1$0$4>2rb$5>2rk$3>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$7$6") := ltac2:(zQ "e0!he!h8!i4!u3!hk9!hs3!hsc!lb!p4!hj9!hl0!hq2!hrc!ht1\2bc$b\2kx$c\4segs@1$1$8\2rb$9\2rk$7\1n$2\2sx$0\5hints@1$1$0\3acc@1$1$aM1\5hints@1$1$0$4^2M2\1n$2$4^4@9$3^9^7@1$5^8^6^5^4^3^2^1\2n0$2@9$3^a^8@3$d^9^7^6^7^6^5^4@1$6$0^2\1b$0\1l@1$1$0@9$3^b^9@1$5^a^8^7^6^5^4^3").

Definition know_lookupABIF : ltac2:(zQ "b0!h8!he!i4!lb!p4!hj9!hk0!hk9!hl0!hq2!hrc>2bc$9>2kx$a>4segs@1$0$4>2kn@1$0$6>2rb$5>2rk$3>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$8$7") := ltac2:(zQ "h20!h8!he!hk9!lb!hl0!hte!hu6!hj9!i4!p4!hud!hvf!ig7!hk0!ih0!ii1!hq2!hrc\2bc$h0\2kx$h1\4segs@1$0$9\2kn@1$0$d\2rb$7\2rk$3\1n$8\2sx$1\5hints@1$0$1\3acc@1$0$4M2\1x$2$2@9$a^a^9^8^6^5^4^3^2^1\1v$7\3scs@1$0$4\6hints0@1$0$1@3$6^3^2^1\4acc'@1$0$4\6hints'@1$0$1M5\1x@1$5@1$0$3$2@5$e^a^9^8^7^6\2bs@1$0$3@3$6@3$f^6^7^1^3^2@2$b^2^1$c").
Section WithSegs.
Variable segs : ltac2:(zQ "20!h8!p4@1$0$1").
Definition sym_readBIF (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABIF bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.

Definition sym_stepBIF (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
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
      match sym_readBIF segs ss bc kx scr a n sx' with
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
        match sym_readBIF segs ss bc kx scr a n (amo_sx wd) with
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
                match sym_readBIF segs ss bc kx scr a n (amo_sx wd) with
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

Definition sym_stepXBIF : ltac2:(zQ "70!i4!il4!ild!im7!in1!hq2!hrc>2bc$5>2kx$6>1K$0>1i$1>2ss$4>3scr$2$3") := ltac2:(zQ "h10!im7!he!ind!io5!ild!in1!h8!i4!il4!itc!iub!iv1!hl0!hq2!hrc!iva!ji2\2bc$d\2kx$e\1K$7\1i$8\2ss$5\3scr$4M0\1x$0$0@6$9^6^5?4segs^3^2^1\3ss'$5\3scs@1$6$c\4scr'$4M1\0$1$0@2$h0@1$3^5@1$3^3@3$a@3$b^7^6^3@5$f?4segs^9^5^3^2^1$2$2").

Fixpoint sym_execTXBIF_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBIF bc kx K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBIF_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.

Definition sym_execTXBIF : ltac2:(zQ "80!i4!in1!he!h8!lb!ji9!hq2!hrc>2bc$6>2kx$7>1t$5>1K$0>4fuel$0>5first$2>5stops@1$3$4>2ss$1$1") := ltac2:(zQ "a0!i4!jj0!he!h8!lb!jj6!ji9!in1!hq2!hrc\2bc$8\2kx$9\1t$6\1K$0\4fuel$0\5first$2\5stops@1$3$4\2ss$7@9$5^8^7^6^5^4^3^2@1$1^1@1$1^1").

(* [comment removed for export] *)
Lemma know_lookupA0IF_eq : ltac2:(zQ "c0!he!h8!i4!jd!lb!hud!hj9!hk9!hl0!hq2!hrc!jkb>2bc$9>2kx$a@3$3>2rb$6>2rk$4>1n$2>2sx$0>5hints@1$1$0>3acc@1$1$8$7@3$5^2^1?4segs@3$b^2^1?4segs").
Proof.
  intros bc kx. apply functional_extensionality; intros rb. apply functional_extensionality; intros rk.
  apply functional_extensionality; intros n. apply functional_extensionality; intros sx.
  apply functional_extensionality; intros hints. apply functional_extensionality; intros acc.
  unfold know_lookupA0IF, know_lookupA0I. rewrite !know_lookupA0F_eq. reflexivity.
Qed.
Lemma know_lookupABIF_eq : ltac2:(zQ "d0!h8!he!i4!jd!lb!jld!hj9!hk0!hk9!hl0!hq2!hrc!jmf>2bc$a>2kx$b@3$3>2kn@1$0$7>2rb$6>2rk$4>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$9$8@3$5^2^1?4segs@3$c^2^1?4segs").
Proof.
  intros bc kx. apply functional_extensionality; intros kn. apply functional_extensionality; intros rb.
  apply functional_extensionality; intros rk. apply functional_extensionality; intros n. apply functional_extensionality; intros sx.
  apply functional_extensionality; intros hints. apply functional_extensionality; intros acc.
  unfold know_lookupABIF, know_lookupABI. rewrite know_lookupA0IF_eq. reflexivity.
Qed.
Lemma sym_readBIF_eq : forall ss bc kx, sym_readBIF segs ss bc kx = sym_readBI segs ss bc kx.
Proof.
  intros ss bc kx. apply functional_extensionality; intros scr. apply functional_extensionality; intros a.
  apply functional_extensionality; intros n. apply functional_extensionality; intros sx'.
  unfold sym_readBIF, sym_readBI. rewrite know_lookupABIF_eq. reflexivity.
Qed.
Lemma sym_stepBIF_eq : ltac2:(zQ "90!jd!il4!itc!ild!im7!in1!hq2!hrc!jo1>2bc$6>2kx$7>1i$1>2ss$5>3scr$3@3$0$4@6$2^5^4?4segs^3^2^1@6$8^5^4?4segs^3^2^1").
Proof. intros. unfold sym_stepBIF, sym_stepBI. rewrite sym_readBIF_eq. reflexivity. Qed.
Lemma sym_stepXBIF_eq : ltac2:(zQ "a0!i4!jd!il4!jof!ild!im7!in1!hq2!hrc!jpf>2bc$7>2kx$8>1K$0>1i$2>2ss$6>3scr$4@3$1$5@6$3^6^5^4^3^2^1@7$9?4segs^6^5^4^3^2^1").
Proof. intros. unfold sym_stepXBIF, sym_stepXBI. rewrite sym_stepBIF_eq. reflexivity. Qed.
Lemma sym_execTXBIF_go_eq : ltac2:(zQ "b0!in1!i4!he!h8!jd!lb!jj6!ji9!hq2!hrc!jqe>2bc$8>2kx$9>1t$7>1K$1>4fuel$1>5first$2>5stops@1$3$5>2ss$0>2ck$0@3$4$0@9$6^9^8^7^6^5^4^3^2^1@a$a?4segs^9^8^7^6^5^4^3^2^1").
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXBIF_go sym_execTXBI_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBIF_eq. destruct (sym_stepXBI segs bc kx K i ss scr_nil) as [ss' scs scr'|]; [|reflexivity].
  destruct scs; [|reflexivity]. apply IH.
Qed.
Lemma sym_execTXBIF_eq : ltac2:(zQ "b0!i4!in1!he!h8!jd!lb!js1!ji9!hq2!hrc!jt2>2bc$8>2kx$9>1t$7>1K$0>4fuel$0>5first$2>5stops@1$3$5>2ss$1@3$4$1@8$6^8^7^6^5^4^3^2^1@9$a?4segs^8^7^6^5^4^3^2^1").
Proof. intros. unfold sym_execTXBIF, sym_execTXBI. apply sym_execTXBIF_go_eq. Qed.

End WithSegs.
End FPX.
End AXF.
