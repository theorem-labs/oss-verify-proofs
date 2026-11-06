(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "sprop"; "sv"; "agree_below"; "holds"; "ss_next"; "ss_facts"; "ss_lenient"; "sprop_below"; "sobj"; "ob_base"; "ob_hi"; "ob_lo"; "ss_pc"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "sv_below"; "eval"; "ob_cells"; "smatch"; "swf"; "mkSS"; "ss_fcsr"; "sv_eqb"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "option"; "nat"; "prod"; "pair"; "Some"; "andb"; "app"; "fst"; "false"; "length"; "snd"; "negb"; "orb"; "None"; "nil"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "iff"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "tripleN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "jpred"; "SP"; "SPJ"; "stableJ"; "ok_frame"; "ok_fault"; "ok_faultJ"; "ok_frameJ"; "LQ"; "LQJ"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.ECfgLex"; "vdir"; "lnode"; "ln_state"; "B64"; "LMAX"; "lex_val"; "comp_val"; "xleq"; "base_val"; "ln_rank"; "echeck2"; "lmeas"; "ln_vars"; "check_ecfg2"; "lex_check"; "to_enodeL"; "to_gnodeL"; "vdir_eqb"; "xle"; "xlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.ECfgAuto"; "vnode"; "vn_state"; "vn_rank"; "to_enode"; "vmeas"; "vn_var"; "echeck"; "check_ecfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.CFGJ"; "enodeJ"; "jnode"; "SPfamJ"; "enj_state"; "SPfamEJ"; "enj_meas"; "enj_pred"; "to_enodeJ"; "edge_okJ"; "nodes_atJ"; "eedge_okJ"; "SPfamGJ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "edge"; "vnode"; "cfg_edges"; "add_facts"; "vn_state"; "enode"; "withG"; "e_leaf"; "e_src"; "e_sub"; "e_tgt"; "gnode"; "SPfamE"; "bind_sv"; "vmeas"; "SPfam"; "edge_ok"; "obj_determined"; "bind_bare"; "bind_list"; "eedge_ok"; "infer_sub"; "take_first"; "vn_rank"; "bind_cells"; "bind_objs"; "check_cfg"; "check_ecfg"; "echeck"; "leaf_matches"; "sv_vars_ok"; "wsub_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "lf_state"; "mkLeaf"; "sv_equiv"; "sym_run"; "uleq"; "sleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_sub"; "wsub_id_below"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.WithSegsE"; "enode"; "en_state"; "en_ghost"; "en_meas"; "SPfamE"; "eedge_ok"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "of_nat"; "mul"; "eqb"; "leb"; "ltb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.WithSegsG"; "gnode"; "edge"; "cuts_edges"; "mkEdge"; "SPfamG"; "cfg_edges"; "e_leaf"; "e_src"; "e_sub"; "e_tgt"; "edge_ok"; "first_match"; "leaves_edges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.WithSegs"; "SPfam"; "leaf_matches"; "forallb_lazy"; "leaf_matches1"; "check_cfg"; "check_cut"; "existsb_lazy"; "@Corelib.Init.Nat"; "sub"; "add";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.WithSegsR"; "nodes_at"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "le"; "ltb"; "@Corelib.Init.Peano"; "le"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "eqb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@Stdlib.Bool.Bool"; "Is_true"; "eqb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep
  SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymComplete SymFrame SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition wsub_bound (s : wsub) (i : positive) : bool := ltac2:(tb__ "0|1|
S35S20S45S3A2M0G0Sc8S25S45S3R1A3Vi;A2Lje;Vs;A3").

Fixpoint sv_vars_ok (ok : positive -> bool) (e : sv) : bool :=
  match e with
  | SVar i => ok i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_vars_ok ok a && sv_vars_ok ok b
  | SExt _ _ a => sv_vars_ok ok a
  | SLBytes _ i _ => sv_vars_ok ok i
  | _ => true
  end.

Fixpoint bind_sv (g : positive) (t l : sv) (acc : wsub) : wsub :=
  let structural :=
    match t, l with
    | SVar i, _ =>
        if Pos.leb g i then (if wsub_bound acc i then acc else (i, l) :: acc) else acc
    | SAlu _ a b, SAlu _ a' b' => bind_sv g b b' (bind_sv g a a' acc)
    | SAluW _ a b, SAluW _ a' b' => bind_sv g b b' (bind_sv g a a' acc)
    | SMd _ a b, SMd _ a' b' => bind_sv g b b' (bind_sv g a a' acc)
    | SMdW _ a b, SMdW _ a' b' => bind_sv g b b' (bind_sv g a a' acc)
    | SExt _ _ a, SExt _ _ a' => bind_sv g a a' acc
    | SExt _ _ a, _ => bind_sv g a l acc
    | SLBytes _ ti _, SLBytes _ li _ => bind_sv g ti li acc
    | _, _ => acc
    end in
  match t with
  | SAlu ALU_ADD a (SVar i) =>
      if Pos.leb g i && negb (wsub_bound acc i)
         && sv_vars_ok (fun v => Pos.ltb v g || wsub_bound acc v) a
      then match rel_offset (sv_subst acc a) l with
           | Some off => (i, off) :: acc
           | None => structural
           end
      else structural

  | SAlu ALU_ADD a (SMd M_MUL (SLit c) (SVar i)) | SAlu ALU_ADD a (SMd M_MUL (SVar i) (SLit c)) =>
      if Pos.leb g i && negb (wsub_bound acc i) && (0 <? c)
         && sv_vars_ok (fun v => Pos.ltb v g || wsub_bound acc v) a
      then match rel_offset (sv_subst acc a) l with
           | Some off =>
               let '(lo, k) := lin_of0 off in
               if forallb (fun ka => fst ka mod c =? 0) lo && (k mod c =? 0)
               then (i, sv_of_lin (map (fun ka => (fst ka / c, snd ka)) lo) (k / c)) :: acc
               else structural
           | None => structural
           end
      else structural
  | _ => structural
  end.

Fixpoint bind_list (g : positive) (ts ls : list sv) (acc : wsub) : wsub :=
  match ts, ls with
  | t :: ts', l :: ls' => bind_list g ts' ls' (bind_sv g t l acc)
  | _, _ => acc
  end.

Definition off_eqb (a b : sv) : bool := sv_eqb a b.

Fixpoint bind_cells (g : positive) (tcs lcs : list cell) (acc : wsub) : wsub :=
  match tcs with
  | [] => acc
  | tc :: rest =>
      let acc' :=
        match List.find (fun lc => off_eqb (c_off lc) (c_off tc) && (c_width lc =? c_width tc)) lcs with
        | Some lc => bind_sv g (c_val tc) (c_val lc) acc
        | None => acc
        end in
      bind_cells g rest lcs acc'
  end.

Definition bind_obj1 (g : positive) (t l : sobj) (acc : wsub) : wsub := ltac2:(tb__ "0|0|
S8bVg;S15Vt;A1S15Vl;A1S80Vg;ScVt;A1ScVl;A1S80Vg;SdVt;A1SdVl;A1S80Vg;SbVt;A1SbVl;A1Vacc;A4A4A4A4").

Fixpoint take_first {A} (f : A -> bool) (l : list A) : option (A * list A) :=
  match l with
  | [] => None
  | x :: rest => if f x then Some (x, rest)
                 else match take_first f rest with
                      | Some (y, rest') => Some (y, x :: rest')
                      | None => None
                      end
  end.

Definition obj_determined (g : positive) (acc : wsub) (e : sv) : bool := ltac2:(tb__ "0|0|
S91S45S2aScaR1Vg;A2S92Vacc;R1A2A2Lv;Ve;A2").

Definition obj_pick (g : positive) (acc : wsub) (t : sobj) (los : list sobj) : option (sobj * list sobj) := ltac2:(tb__ "0|8|
S1cS1eS20SaS1bSaA1A2M0A1M1L_;M2S84Vg;Vacc;SbVt;A1M3A3S9eVacc;G3A2S3SaS97SbR1A1R2A2Ll;SaS1cFl;M4SaS23S23R2R1A1S97SdR1A1S9eVacc;SdVt;A1M5A2A2A2S97ScR1A1S9eVacc;ScVt;A1M6A2A2A2Ll;G4G1G1Lx;G2S23S84Vg;Vacc;G5A3S84Vg;Vacc;G6A3A2S89SaR1Vlos;A3S2bG0A1M7X1cx2G0S22G0R1A2Lr;S89SaR2Vlos;A3X1ex2Tsame_all;Tsame_base;Ttb;G7X1cx2").

Fixpoint bind_objs (g : positive) (tos los : list sobj) (acc : wsub) : wsub :=
  match tos with
  | [] => acc
  | t :: ts' =>
      match obj_pick g acc t los with
      | Some (l, rest) => bind_objs g ts' rest (bind_obj1 g t l acc)
      | None =>
          match los with
          | l :: ls' => bind_objs g ts' ls' (bind_obj1 g t l acc)
          | [] => acc
          end
      end
  end.

Fixpoint bind_bare (g : positive) (ts ls : list sv) (acc : wsub) : wsub :=
  match ts, ls with
  | t :: ts', l :: ls' =>
      bind_bare g ts' ls'
        match t with
        | SVar i => if Pos.leb g i && negb (wsub_bound acc i) then (i, l) :: acc else acc
        | _ => acc
        end
  | _, _ => acc
  end.

Definition infer_sub (g : positive) (L T : sstate) : wsub := ltac2:(tb__ "0|5|
S85Vg;S11VT;A1M0S11VL;A1M1S2cS20S45S3A2A1A4S9bS85Vg;SfVT;A1M2SfVL;A1M3R1A4S9bS86Vg;G0G1R1A4S9bS86Vg;G2G3R1A4S9bS1eS3A1S9bLx;M4S12VT;A1S3G4S12VL;A1S3S80Vg;R2R1R3A4Ll;R2X1ex2Lt;R1X1ex2S9bS8cVg;S10VT;A1S10VL;A1R1A4Tacc;Tacc;Tacc;Tacc;Tacc;").

Section WithSegs.
Variable segs : list Segment.

Fixpoint existsb_lazy {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | x :: t => if f x then true else existsb_lazy f t end.
Fixpoint forallb_lazy {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => true | x :: t => if f x then forallb_lazy f t else false end.

Lemma existsb_lazy_eq : forall {A} (f : A -> bool) l, existsb_lazy f l = existsb f l.
Proof using . intros A f l. induction l as [|x t IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.
Lemma forallb_lazy_eq : forall {A} (f : A -> bool) l, forallb_lazy f l = forallb f l.
Proof using . intros A f l. induction l as [|x t IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.

Definition leaf_matches1 (g : positive) (L X : sstate) : bool := ltac2:(tb__ "0|1|
S1cS1cL_;M0SabSeVL;A1SeVX;A1A2S88Vg;VL;VX;A3S9bG0S9dR1Vg;A2SafVL;VX;R1A3S26X1cx2Ts;S26X1cx2").

Definition leaf_matches (g : positive) (L : sstate) (targets : list sstate) : bool := ltac2:(tb__ "0|0|
Sc3S0Sc0Vg;VL;A2Vtargets;A3").

Lemma leaf_matches1_true : ltac2:(tb__ "0|1|
S45S0S0S2dS1cSc0R3R2R1A3S1dA3S2eS2dS1cS9dS88R4R3R2A3M0R4A2S1dA3S2dS1cSafR3R2G0A3S1dA3A2F_;FX;FL;Fg;").
Proof using .
  intros g L X H. unfold leaf_matches1 in H.
  destruct (ss_pc L =? ss_pc X); [|discriminate].
  destruct (wsub_id_below (infer_sub g L X) g); [|discriminate]. auto.
Qed.

Definition check_cut (fuel : nat) (cutpcs : list Z) (g : positive)
           (targets : list sstate) (T : sstate) : bool := ltac2:(tb__ "0|1|
S1cS1cL_;Sc7Vg;S6VT;A1A2S1eS1bS93A1M0A1S1cLx;S98Vsegs;Vfuel;Vcutpcs;VT;S1dA5G0SbfS93S93SbeVg;S95R1A1Vtargets;A3LL;R1A3Lleaves;S26X1ex2S26X1cx2").

Definition check_cfg (fuel : nat) (cutpcs : list Z) (g : positive)
           (cuts exits : list sstate) : bool := ltac2:(tb__ "0|0|
SbfS0Sc2Vfuel;Vcutpcs;Vg;S24S0Vcuts;Vexits;A3A4Vcuts;A3").

Definition cfg_residual (fuel : nat) (cutpcs : list Z) (g : positive)
           (cuts exits : list sstate) : list (Z * option (list leaf)) := ltac2:(tb__ "0|3|
S47S0S20S46S1eS1bS93A1M0A1M1A2S0S21S46G1SeR1A1G1G1Lx;S98Vsegs;Vfuel;Vcutpcs;R1S1dA5G0S22G0Sd4S93G0Sd6S93A1S93Sd2S29SbeVg;S95R1A1S24S0Vcuts;Vexits;A3A3A1M2A1LL;S93Sd5G2A1Lx;R1A6A2Lleaves;S2bG0A1X1ex2A4LT;Vcuts;A4").

Definition SPfam (K : list event -> Model -> Prop) (G : valuation -> Prop)
           (fam : list sstate) : assn := ltac2:(tb__ "0|0|
S36S2fS0S0S2fS1S1S2eS32S0R2Vfam;A3S2eVG;R1A1S3cVsegs;VK;R2R1R3A5A2A2Lrho;A2LT;A2Lw;").

Lemma SPfam_app : ltac2:(tb__ "0|1|
S1bS71A1S72OF_;F_;S1OF_;S1bS0A1M0G0S36S31SbdR5R4S24S0R3R2A3R1A4S30SbdR5R4R3R1A4SbdR5R4R2R1A4A2A2Fw;Ff2;Ff1;FG;FK;").
Proof using .
  intros K G f1 f2 w. unfold SPfam. split.
  - intros (T & rho & Hin & Hg & Hsp). apply in_app_or in Hin as [Hin|Hin];
      [left|right]; exists T, rho; auto.
  - intros [(T & rho & Hin & Hg & Hsp)|(T & rho & Hin & Hg & Hsp)];
      exists T, rho; (split; [apply in_or_app; auto|auto]).
Qed.

Lemma leaf_matches_sound : ltac2:(tb__ "0|0|
S1bS71A1S72OF_;F_;S1OFx;S45S0S1bS0A1S1S36S1S1R8R2A1S4R8R3R2A3RaR3A1F_;F_;Frho';Frho;S2dS1cSbeR6R5R4A3S1dA3R8R4A1S3cVsegs;RaR7R5R4A5SbdRbRaR7R5A4F_;F_;F_;F_;Fw;Frho;Ftargets;FL;Fg;FG;FK;").
Proof using .
  intros K G g L targets rho w HG Hm Hg Hsp.
  unfold leaf_matches in Hm. rewrite existsb_lazy_eq in Hm. apply existsb_exists in Hm as (X & Hin & Hm).
  apply leaf_matches1_true in Hm as [Hid He].
  exists X, (rho_sub rho (infer_sub g L X)). split; [exact Hin|]. split.
  - eapply HG; [exact Hg|]. apply rho_sub_agree. exact Hid.
  - eapply SP_entails; eauto.
Qed.

Theorem cfg_sound : ltac2:(tb__ "0|1|
S1fS1bS46A1S45S1bS0A1M0G0S1OF_;S36OF_;S1bS71A1S72OF_;F_;S39S3fVsegs;R3R2A3S2dS1cS35S0S8R7A3S1dA3S40Vsegs;R5R4A3F_;S1S1R8R2A1S4RcR3R2A3RaR3A1F_;F_;Frho';Frho;S2dS1cSc1RcRbRaR9R8A5S1dA3S0S1S32S0R2RbA3RbR2A1S37Vsegs;RbS3cVsegs;RaR4R3A4S36S30SbdRbRdRfR1A4RaR1A1A2Lw;A4F_;F_;Frho;FE;S0S1S32S0R2RdA3RcR2A1S37Vsegs;RcS3cVsegs;RbR4R3A4RaA4F_;F_;Frho;FT;F_;F_;F_;F_;F_;FQ;FK;Fok;FG;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits G ok K Q Hok Hokf HG Hchk Hexits T rho HinT Hg.

  assert (Hloop : triple segs ok (SPfam K G cuts) Q).
  { apply triple_loop.
    unfold SPfam at 1. apply triple1_ex; intros T'. apply triple1_ex; intros rho'.
    apply triple1_pure; intros HinT'. apply triple1_pure; intros Hg'.
    unfold check_cfg in Hchk. rewrite forallb_lazy_eq in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk T' HinT') as Hc.
    unfold check_cut in Hc. destruct (Pos.leb g (ss_next T')) eqn:Hle; [|discriminate]. apply Pos.leb_le in Hle.
    destruct (sym_run segs fuel cutpcs T' true) as [leaves|] eqn:Hrun; [|discriminate]. rewrite forallb_lazy_eq in Hc.
    eapply triple1_seq_l.
    { eapply sym_run_sound; eauto. intros Hlen. apply Hokf.
      apply existsb_exists. exists T'. auto. }

    intros m Hgm w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hk).
    pose proof (proj1 (forallb_forall _ _) Hc L HinL) as HmL.
    assert (Hg'' : G rho'') by (eapply HG; [exact Hg'|]; eapply agree_below_le; [exact Hle|exact Hag]).
    pose proof (leaf_matches_sound K G g (lf_state L) (cuts ++ exits) rho'' w HG HmL Hg''
                  (conj Hsm Hk)) as Hfam.
    apply SPfam_app in Hfam as [Hcut|Hexit].
    - exact (Hgm w (or_introl Hcut)).
    - destruct Hexit as (E & rhoE & HinE & HgE & HspE).
      exact (Hexits E rhoE HinE HgE m Hgm w HspE). }
  eapply triple_conseq; [| intros w Hw; exact Hw | exact Hloop].
  intros w Hw. exists T, rho. auto.
Qed.

End WithSegs.

Section WithSegsG.
Variable segs : list Segment.

Definition gnode : Type := ltac2:(tb__ "0|0|
S20S0S1OF_;A2").

Fixpoint first_match (g : positive) (L : sstate) (targets : list sstate) (j : nat) : option (nat * wsub) :=
  match targets with
  | [] => None
  | X :: rest =>
      if leaf_matches1 g L X then Some (j, infer_sub g L X)
      else first_match g L rest (S j)
  end.

Record edge := mkEdge { e_src : nat; e_leaf : sstate; e_tgt : nat; e_sub : wsub }.

Fixpoint leaves_edges (g : positive) (i : nat) (leaves : list leaf) (targets : list sstate) : option (list edge) :=
  match leaves with
  | [] => Some []
  | L :: rest =>
      match first_match g (lf_state L) targets 0, leaves_edges g i rest targets with
      | Some (j, s), Some es => Some (mkEdge i (lf_state L) j s :: es)
      | _, _ => None
      end
  end.

Fixpoint cuts_edges (fuel : nat) (cutpcs : list Z) (g : positive) (i : nat)
         (cuts : list sstate) (targets : list sstate) : option (list edge) :=
  match cuts with
  | [] => Some []
  | T :: rest =>
      if negb (Pos.leb g (ss_next T)) then None else
      match sym_run segs fuel cutpcs T true with
      | Some leaves =>
          match leaves_edges g i leaves targets, cuts_edges fuel cutpcs g (S i) rest targets with
          | Some es, Some es' => Some (es ++ es')
          | _, _ => None
          end
      | None => None
      end
  end.

Definition cfg_edges (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list sstate) : option (list edge) := ltac2:(tb__ "0|0|
Sb2Vfuel;Vcutpcs;Vg;U0Vcuts;S24S0Vcuts;Vexits;A3A6").

Definition edge_ok (nodes : list gnode) (e : edge) : Prop := ltac2:(tb__ "0|3|
Sb0Sb0S2dS1eSb0A1M0S34Sb0Vnodes;Sb7Ve;A1A3S22Sb0R2A2M1A3S2dG0S34Sb0Vnodes;Sb9Ve;A1A3G1A3S1S1S4S6S25S0S1OF_;M2R6A3A1R2R1A3S28S0G2R7R3A4S48S2S5R3A1S7Sb6Ve;A1A1A3S28S0G2R8S9cR4Sb8Ve;A1A2A4F_;F_;F_;Frho';Frho;F_;F_;FTj;FTi;").

Definition SPfamG (K : list event -> Model -> Prop) (nodes : list gnode) : assn := ltac2:(tb__ "0|1|
S36S2fS0S0S2fS1OF_;M0G0S2fS1S1S2eS32S20S0G0A2S21S0G0R3R2A4Vnodes;A3S2eR2R1A1S3cVsegs;VK;R3R1R4A5A2A2Lrho;A2LG;A2LT;A2Lw;").

Lemma first_match_spec : ltac2:(tb__ "0|1|
S45S0S1bS0A1S1fS1fS9bS2dS1eS20S1fS9bA2M0A1SbbR6R5R4R3A4S22G0S21S1fS9bR2R1A4A2A3S2fS0S0S2eS2dS1eS0A1S34S0R6Sc4R4R5A2A3S22S0R1A2A3S2eScbR5R4A2S2eS2dS1cS9dR3R8A2S1dA3S2dS1cSafR7R1R3A3S1dA3A2A2A2LX;A2F_;Fs;Fj;Fj0;Ftargets;FL;Fg;").
Proof using .
  induction targets as [|X rest IH]; intros j0 j s H; cbn in H; [discriminate|].
  destruct (leaf_matches1 g L X) eqn:E.
  - injection H as <- <-. exists X. rewrite Nat.sub_diag. apply leaf_matches1_true in E as [A B]. repeat split; auto.
  - destruct (IH (S j0) j s H) as (X' & Hn & Hle & A & B). exists X'.
    replace (j - j0)%nat with (S (j - S j0))%nat by lia. cbn. repeat split; auto. lia.
Qed.

Lemma leaves_edges_spec : ltac2:(tb__ "0|2|
S45S1fS1bS93A1S1bS0A1S1bSb1A1M0S2dS1eG0A1SbcR5R4R3R2A4S22G0R1A2A3S93S32S93R1R5A3S2fS1fS1fS2fS9bS9bS2fS0S0S2eS32Sb1Sb3RaS95R5A1M1R3R2A4R7A3S2eS2dS1eS0A1S34S0R8R3A3S22S0R1A2A3S2eS2dS1cS9dR2RbA2S1dA3S2dS1cSafG1R1R2A3S1dA3A2A2A2LX;A2Ls;A2Lj;A2F_;FL;F_;Fes;Ftargets;Fleaves;Fi;Fg;").
Proof using .
  induction leaves as [|L0 rest IH]; intros targets es H L Hin; cbn in H; [destruct Hin|].
  destruct (first_match g (lf_state L0) targets 0) as [[j s]|] eqn:Hm; [|discriminate].
  destruct (leaves_edges g i rest targets) as [es'|] eqn:He; [|discriminate]. injection H as <-.
  destruct Hin as [<-|Hin].
  - destruct (first_match_spec g (lf_state L0) targets 0 j s Hm) as (X & Hn & _ & A & B).
    rewrite Nat.sub_0_r in Hn. exists j, s, X. split; [cbn; auto|]. auto.
  - destruct (IH targets es' He L Hin) as (j' & s' & X & Hin' & Hn & A & B).
    exists j', s', X. split; [cbn; auto|]. auto.
Qed.

Lemma cuts_edges_spec : ltac2:(tb__ "0|6|
S1fS1bS46A1S45S1bS0A1M0S1fG0S1bSb1A1M1S2dS1eG1A1Sb2R7R6R5R3R4R2A6S22G1R1A2A3S1fS0S2dS1eS0A1M2S34S0R7R2A3S22S0R1A2M3A3S2eSc9R9S6R2A1A2S2fS1bS93A1M4G4S2eS2dS1eG4A1S98Vsegs;RcRbR3S1dA5S22G4R1A2A3S93S32S93R1R2A3S2fS1fS1fS2fS9bS9bS2fS0S0S2eS32Sb1Sb3Sc5RdR9A2S95R5A1M5R3R2A4RbA3S2eS2dG2S34S0RcR3A3G3A3S2eS2dS1cS9dR2RfA2S1dA3S2dS1cSafG5R1R2A3S1dA3A2A2A2LX;A2Ls;A2Lj;A2F_;FL;A2Lleaves;A2A2F_;FT;Fk;F_;Fes;Ftargets;Fi0;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  induction cuts as [|T0 rest IH]; intros i0 targets es H k T Hn; [destruct k; discriminate|].
  cbn in H. destruct (Pos.leb g (ss_next T0)) eqn:Hg; cbn in H; [|discriminate].
  destruct (sym_run segs fuel cutpcs T0 true) as [leaves|] eqn:Hrun; [|discriminate].
  destruct (leaves_edges g i0 leaves targets) as [es1|] eqn:He1; [|discriminate].
  destruct (cuts_edges fuel cutpcs g (S i0) rest targets) as [es2|] eqn:He2; [|discriminate].
  injection H as <-.
  destruct k as [|k].
  - cbn in Hn. injection Hn as ->. split; [apply Pos.leb_le; exact Hg|].
    exists leaves. split; [exact Hrun|]. intros L HinL.
    destruct (leaves_edges_spec g i0 leaves targets es1 He1 L HinL) as (j & s & X & A & B & C & D).
    exists j, s, X. rewrite Nat.add_0_r. split; [apply in_or_app; left; exact A|]. auto.
  - cbn in Hn. destruct (IH (S i0) targets es2 He2 k T Hn) as (Hg' & leaves' & Hrun' & HL).
    split; [exact Hg'|]. exists leaves'. split; [exact Hrun'|]. intros L HinL.
    destruct (HL L HinL) as (j & s & X & A & B & C & D). exists j, s, X.
    replace (i0 + S k)%nat with (S i0 + k)%nat by lia. split; [apply in_or_app; right; exact A|]. auto.
Qed.

Theorem cfg_sound_gen : ltac2:(tb__ "0|7|
S1fS1bS46A1S45S1bSb0A1M0G0S1bSb1A1M1S36OF_;S1bS71A1S72OF_;F_;S39S3fVsegs;R3R2A3S2dS1cS35S20S0S1OF_;M2A2M3G3S8S25S0G2R1A3A1LTG;R7A3S1dA3S40Vsegs;R5R4A3F_;S2dS1eG1A1Sb5RbRaR9S47G3S0S25S0G2A2M4R8A4S47G3S0G4R7A4A5S22G1R6A2A3S48Sb1SbaS24Sb0R9R8A3A1R7A3S0G2S1S32G3S21S0G2R3R2A4M5RcA3R3R2A1M6S37Vsegs;RcS3cVsegs;RbR5R3A4S36S30Sb4RcR10R1A3RbR1A1A2Lw;A4F_;F_;Frho;FGE;FE;S0G2S1S32G3G5ReA3G6S37Vsegs;RdS3cVsegs;RcR5R3A4RbA4F_;F_;Frho;FG;FT;F_;F_;F_;F_;F_;FQ;FK;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok K Q Hok Hokf Hes Hedges Hexits T G rho HinT Hg.
  assert (Hloop : triple segs ok (SPfamG K cuts) Q).
  { apply triple_loop.
    unfold SPfamG at 1. apply triple1_ex; intros T'. apply triple1_ex; intros G'. apply triple1_ex; intros rho'.
    apply triple1_pure; intros HinT'. apply triple1_pure; intros Hg'.
    destruct (In_nth_error _ _ HinT') as [k Hk].
    assert (HkT : nth_error (map fst cuts) k = Some T') by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edges in Hes.
    destruct (cuts_edges_spec fuel cutpcs g (map fst cuts) 0 (map fst cuts ++ map fst exits) es Hes k T' HkT)
      as (Hle & leaves & Hrun & HL).
    eapply triple1_seq_l.
    { eapply sym_run_sound; eauto. intros Hlen. apply Hokf. apply existsb_exists. exists (T', G'). split; [exact HinT'|exact Hlen]. }
    intros m Hgm w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent).
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold edge_ok in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold gnode in *.
    destruct (nth_error (cuts ++ exits) j) as [[Xs GX]|] eqn:HnXG; cbn in HnX; [|discriminate].
    injection HnX as ->.
    assert (HGX : GX (rho_sub rho'' s)).
    { eapply (EOK (T', G') (X, GX)); [| reflexivity | exact Hag | exact Hg' |].
      - rewrite nth_error_app1; [exact Hk|]. apply nth_error_Some. congruence.
      - destruct w as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
    pose proof (SP_entails segs K (lf_state L) X s rho'' w Hent (conj Hsm Hkk)) as HSPX.
    destruct (Nat.lt_ge_cases j (length cuts)) as [Hj|Hj].
    -
      apply Hgm. left. exists X, GX, (rho_sub rho'' s). split; [|split; [exact HGX|exact HSPX]].
      rewrite nth_error_app1 in HnXG by exact Hj. eapply nth_error_In; eauto.
    -
      rewrite nth_error_app2 in HnXG by exact Hj.
      exact (Hexits X GX (rho_sub rho'' s) (nth_error_In _ _ HnXG) HGX m Hgm w HSPX). }
  eapply triple_conseq; [| intros w Hw; exact Hw | exact Hloop].
  intros w Hw. exists T, G, rho. auto.
Qed.

End WithSegsG.

From Stdlib Require Import Zwf Wellfounded.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegsE.
Variable segs : list Segment.

Definition enode : Type := ltac2:(tb__ "0|0|
S20S20S0S1OF_;A2S1S46F_;A2").
Definition en_state (n : enode) : sstate := fst (fst n).
Definition en_ghost (n : enode) : valuation -> Prop := snd (fst n).
Definition en_meas (n : enode) : valuation -> Z := snd n.

Definition eedge_ok (nodes : list enode) (e : edge) : Prop := ltac2:(tb__ "0|4|
S9fS9fS2dS1eS9fA1M0S34S9fVnodes;S7bVe;A1A3S22S9fR2A2M1A3S2dG0S34S9fVnodes;S7dVe;A1A3G1A3S1S1S4S6Sa0R6A1A1R2R1A3Sa1R7R3A2S48S2S5R3A1S7S7aVe;A1A1A3S2eSa1R8S9cR4S7cVe;A1A2M2A2S2eSa5Z0Sa2R8G2A2M3A2Sa6G3Sa2R9R5A2A2A2A2F_;F_;F_;Frho';Frho;F_;F_;FTj;FTi;").

Definition SPfamE (K : list event -> Model -> Prop) (nodes : list enode) (bound : Z) : world -> Prop := ltac2:(tb__ "0|1|
S36S2fS9fS9fS2fS1S1S2eS32S9fR2Vnodes;A3S2eSa1R2R1A2S2eS3cVsegs;VK;Sa0R2A1R1R3A5S2eSa5Z0Sa2R2R1A2M0A2Sa6G0Vbound;A2A2A2A2A2Lrho;A2Ln;A2Lw;").

Theorem cfg_complete_gen : ltac2:(tb__ "0|4|
S1fS1bS46A1S45S1bS9fA1M0G0S1bS73A1M1S1bS71A1S72OF_;F_;S36OF_;S2dS1cS33S9fS9fS29S8Sa0R1A1A1A1Ln;R5A3S1dA3S2dS1eG1A1S75Vsegs;R9R8R7S47S9fS0Sa0R6A4S47S9fS0Sa0R5A4A6S22G1R4A2A3S48S73Sa4S24S9fR7R6A3A1R5A3S9fS1S32S9fR2R9A3Sa1R3R2A2M2S38Vsegs;S3cVsegs;R9Sa0R4A1M3R3A4S36S30Sa3RaRdSa2R5R4A2R1A4R9R1A1A2Lw;A3F_;F_;Frho;FE;S9fS1S32S9fR2RbA3G2S38Vsegs;S3cVsegs;RaG3R3A4R9A3F_;F_;Frho;Fn;F_;F_;F_;F_;FQ;FK;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es K Q Hstrict Hes Hedges Hexits n rho Hin Hg.
  set (I := fun (a : Z) (w : world) =>
              exists n rho, In n (cuts ++ exits) /\ en_ghost n rho /\ SP segs K (en_state n) rho w /\ en_meas n rho = a /\ 0 <= a).
  assert (BODY : forall a, etriple segs (I a) (fun w => (exists a', (Zwf 0 a' a) /\ I a' w) \/ Q w)).
  { intros a w (n0 & rho0 & Hin0 & Hg0 & Hsp0 & Hm0 & Ha0).
    apply in_app_or in Hin0 as [Hcut|Hexit].
    -
      destruct (In_nth_error _ _ Hcut) as [k Hk].
      assert (HkT : nth_error (map en_state cuts) k = Some (en_state n0)) by (rewrite nth_error_map, Hk; reflexivity).
      unfold cfg_edges in Hes.
      destruct (cuts_edges_spec segs fuel cutpcs g (map en_state cuts) 0 (map en_state cuts ++ map en_state exits) es Hes k _ HkT)
        as (Hle & leaves & Hrun & HL).
      assert (Hlen : ss_lenient (en_state n0) = false).
      { pose proof (proj1 (forallb_forall _ _) Hstrict n0 Hcut) as X. cbn beta in X. destruct (ss_lenient (en_state n0)); [cbn in X; discriminate|reflexivity]. }
      destruct (sym_run_etriple segs fuel cutpcs (en_state n0) leaves K rho0 Hlen Hrun w Hsp0) as (w' & Hsteps & HLQ).
      destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
      destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent). rewrite Nat.add_0_l in HinE.
      pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_ok in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
      rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold enode in *.
      destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate]. injection HnX as HX.
      assert (FACTS : Forall (holds rho'') (ss_facts (lf_state L))).
      { destruct w' as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
      destruct (EOK n0 nj ltac:(rewrite nth_error_app1; [exact Hk| apply nth_error_Some; congruence]) eq_refl rho0 rho'' Hag Hg0 FACTS) as [HGj HMj].
      pose proof (SP_entails segs K (lf_state L) X s rho'' w' Hent (conj Hsm Hkk)) as HSPX. rewrite <- HX in HSPX.
      exists w'. split; [exact Hsteps|]. left. exists (en_meas nj (rho_sub rho'' s)). split.
      + unfold Zwf. lia.
      + exists nj, (rho_sub rho'' s). split; [eapply nth_error_In; exact HnXG|].
        split; [exact HGj|]. split; [exact HSPX|]. split; [reflexivity|lia].
    -
      destruct (Hexits n0 rho0 Hexit Hg0 w Hsp0) as (w' & Hsteps & [Hfam|Hq]).
      + destruct Hfam as (n1 & rho1 & Hin1 & Hg1 & Hsp1 & Hm1).
        exists w'. split; [exact Hsteps|]. left. exists (en_meas n1 rho1). split; [unfold Zwf; lia|].
        exists n1, rho1. split; [apply in_or_app; left; exact Hin1|].
        split; [exact Hg1|]. split; [exact Hsp1|]. split; [reflexivity|lia].
      + exists w'. split; [exact Hsteps|]. right. exact Hq. }
  pose proof (@etriple_loop segs Z (Zwf 0) (Zwf_well_founded 0) I Q BODY) as LOOP.
  intros w Hw.
  destruct (Z_lt_le_dec (en_meas n rho) 0) as [Hneg|Hnn].
  -

    exfalso.
    destruct (In_nth_error _ _ Hin) as [k Hk].
    assert (HkT : nth_error (map en_state cuts) k = Some (en_state n)) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edges in Hes.
    destruct (cuts_edges_spec segs fuel cutpcs g (map en_state cuts) 0 (map en_state cuts ++ map en_state exits) es Hes k _ HkT)
      as (Hle & leaves & Hrun & HL).
    assert (Hlen : ss_lenient (en_state n) = false).
    { pose proof (proj1 (forallb_forall _ _) Hstrict n Hin) as X. cbn beta in X. destruct (ss_lenient (en_state n)); [cbn in X; discriminate|reflexivity]. }
    destruct (sym_run_etriple segs fuel cutpcs (en_state n) leaves K rho Hlen Hrun w Hw) as (w' & Hsteps & HLQ).
    destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent). rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_ok in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold enode in *.
    destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate].
    assert (FACTS : Forall (holds rho'') (ss_facts (lf_state L))).
    { destruct w' as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
    destruct (EOK n nj ltac:(rewrite nth_error_app1; [exact Hk| apply nth_error_Some; congruence]) eq_refl rho rho'' Hag Hg FACTS) as [_ HMj].
    lia.
  - apply (LOOP (en_meas n rho)). exists n, rho. split; [apply in_or_app; left; exact Hin|].
    split; [exact Hg|]. split; [exact Hw|]. split; [reflexivity|lia].
Qed.

End WithSegsE.

Definition add_facts (F : list sprop) (S : sstate) : sstate := ltac2:(tb__ "0|0|
S18SeVS;A1S11VS;A1SfVS;A1S19VS;A1S12VS;A1S10VS;A1S24S2VF;S7VS;A1A3S6VS;A1S8VS;A1A9").

Lemma swf_add_facts : ltac2:(tb__ "0|0|
S1bS2A1S0S2dS1cS17R1A1S1dA3S2dS1cS33S2S9S6R2A1A1R3A3S1dA3S2dS1cS17S76R4R3A2A1S1dA3F_;F_;FS;FF;").
Proof.
  intros F S H HF. unfold swf in *. cbn [add_facts ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts].
  apply andb_prop in H as [H Hfacts]. rewrite H. cbn [andb].
  rewrite forallb_app. rewrite HF, Hfacts. reflexivity.
Qed.

Lemma smatch_add_facts : ltac2:(tb__ "0|0|
S1bSd0A1S1S1bS2A1S0S20S1bS71A1Sd1A2S16R5R4R2R1A4S48S2S5R5A1R4A3S2dS1cS33S2S9S6R4A1A1R5A3S1dA3S16R8R7S76R6R5A2R4A4F_;F_;F_;Fw;FS;FF;Frho;Fsegs;").
Proof.
  intros segs rho F S [tr [ms md]] Hsm HF Hb.
  pose proof Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  unfold smatch. cbn [fst snd cfg_ms cfg_model add_facts ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  split; [apply swf_add_facts; assumption|].
  repeat (split; [assumption|]). apply Forall_app. split; assumption.
Qed.

Section Glue.
Variable segs : list Segment.

Lemma SP_entails_sem : ltac2:(tb__ "0|0|
S1bS71A1S72OF_;F_;S0S0S1bS2A1S9bS1S36S2dS1cSafR6R5R3A3S1dA3S2dS1cS33S2S9S6R6A1A1R5A3S1dA3S1S48S2S5R1A1S7R9A1A3S48S2S5S9cR2R7A2A1R8A3F_;Frho;S3cVsegs;RaR9R5R4A5S3cVsegs;RbS76R8R9A2S9cR6R7A2R5A5F_;F_;F_;F_;Fw;Frho;Fs;FF;FT0;FL;FK;").
Proof using .
  intros K L T0 F s rho w He Hb HF [Hsm Hk]. split; [|exact Hk].
  apply smatch_add_facts; [eapply entails_sound; eauto | | exact Hb].
  apply HF. destruct w as [tr [ms md]].
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma exit_reenter : ltac2:(tb__ "0|0|
S36OF_;S1bS71A1S72OF_;F_;S1OF_;S45S1bS0A1S39S0S0S1bS2A1S9bS32S0S76R2R3A2R6A3S2dS1cSafR5R4R2A3S1dA3S2dS1cS9dR3R9A2S1dA3S1S1RdR2A1S4RdR3R2A3RfR3A1F_;F_;Frho';Frho;S2dS1cS33S2S9S6R7A1A1R6A3S1dA3S1S48S2S5R1A1S7RaA1A3S48S2S5S9cR2R8A2A1R9A3F_;Frho;S1RfR1A1S37Vsegs;R12S3cVsegs;R11RcR2A4S36S30S82Vsegs;R12R11RfR1A5ReR1A1A2Lw;A4F_;Frho;F_;F_;F_;F_;F_;F_;Fs;FF;FT0;FE;FQ;Fcuts;Fg;FG;FK;Fok;").
Proof using .
  intros ok K G g cuts Q E T0 F s Hin He Hid HG Hb HF rho Hg.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hsp. left. exists (add_facts F T0), (rho_sub rho s).
  split; [exact Hin|]. split.
  - eapply HG; [exact Hg|]. apply rho_sub_agree. exact Hid.
  - eapply SP_entails_sem; eauto.
Qed.

Lemma exit_post : ltac2:(tb__ "0|0|
S36OF_;S1bS71A1S72OF_;F_;S45S1S1bS0A1S1bS93A1S0S32S93S96R1S94A2R2A3S1S4R7R6R1A3S37Vsegs;RaS3cVsegs;R9R4R2A4S36S30S82Vsegs;RaS1S4RaR9R1A3Lr;R7R1A5S43Vsegs;RaR9R8R6R1A6A2Lw;A4F_;Frho;F_;FP;Fposts;Fcuts;Frho0;Fn;FK;Fok;").
Proof using .
  intros ok K n rho0 cuts posts P Hin rho Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w [Hsm Hk]. right. exists (mkLeaf P RsSymJump), rho. auto.
Qed.

End Glue.

Section ECfgAuto.
Variable segs : list Segment.

Record vnode := mkVN { vn_state : sstate; vn_rank : Z; vn_var : sv }.

Definition vmeas (n : vnode) (rho : valuation) : Z := ltac2:(tb__ "0|0|
Sa8SaaS5fVn;A1Sa7Z2Z40A2A2SceQ40S14Vrho;S62Vn;A1A2A2A2").

Definition to_enode (G : valuation -> Prop) (n : vnode) : enode := ltac2:(tb__ "0|1|
S21S20S0S1OF_;M0A2S1S46Frho;S21S0G0S5eVn;A1VG;A4S61Vn;A1A4").

Definition echeck (g : positive) (nodes : list vnode) (e : edge) : bool := ltac2:(tb__ "0|6|
S1eS5dA1S1cLx;M0S34S5dVnodes;S7bVe;A1A3S5dG0S34S5dVnodes;S7dVe;A1A3S5dS23S23S23S23S9dS7cVe;A1M1Vg;A2Sc7Vg;S6S5eR2A1A1M2A2A2S13G2S62R2A1M3A2A2SacZ0S5fR1A1M4A2A2S2aSadG4S5fR2A1M5A2S23SabG4G5A2S99S7S7aVe;A1A1S9eG1S62R1A1A2Z1G3A4A2A2A2Lnj;S26X1ex2Lni;S26X1ex2").

Definition check_ecfg (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list vnode) : bool := ltac2:(tb__ "0|1|
S23S33S5dS5dS29S8S5eR1A1A1A1Ln;Vcuts;A3S1eS1bS73A1M0A1S1cLx;S75Vsegs;Vfuel;Vcutpcs;Vg;S47S5dS0S5eVcuts;A4S47S5dS0S5eVexits;A4A6G0S33S73S63Vg;S24S5dVcuts;Vexits;A3A2R1A3Les;S26X1ex2A2").

Lemma echeck_sound : ltac2:(tb__ "0|0|
S45S1OF_;S1bS5dA1S73S1S1R5R2A1S4R7R3R2A3R7R3A1F_;F_;Fr2;Fr1;S2dS1cS63R5R3R2A3S1dA3S87S47S5dS78S60R5A1R4A4R3A2F_;F_;Fe;Fnodes;FG;Fg;").
Proof using .
  intros g G nodes e HG H. unfold echeck in H. unfold eedge_ok.
  intros Ti Tj Hi Hj rho rho' Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enode en_state en_ghost en_meas fst snd] in *.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H Hrk].
  apply andb_prop in H as [H Hvb]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle. apply Z.leb_le in Hrk.
  split.
  - eapply HG; [exact Hg|]. eapply agree_below_trans.
    + eapply agree_below_le; [exact Hgle | exact Hag].
    + apply rho_sub_agree. exact Hid.
  - unfold vmeas. rewrite <- eval_subst.
    rewrite (eval_agree _ rho rho' (vn_var ni) Hag Hvb).
    pose proof (urange (eval rho' (sv_subst (e_sub e) (vn_var nj)))) as R1.
    pose proof (urange (eval rho' (vn_var ni))) as R2.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + apply Z.ltb_lt in Hlt. nia.
    + apply andb_prop in Heq as [Heq Hu]. apply Z.eqb_eq in Heq.
      pose proof (uleq_sound rho' _ _ 1 _ HF Hu) as U1. unfold U in U1. rewrite Heq. lia.
Qed.

Theorem cfg_complete_auto : ltac2:(tb__ "0|2|
S1fS1bS46A1S45S1bS5dA1M0G0S1OF_;S1bS71A1S72OF_;F_;S36OF_;S1S1R5R2A1S4R9R3R2A3R7R3A1F_;F_;Fr2;Fr1;S2dS1cS64R9R8R7R6R5A5S1dA3S5dS1S32S5dR2R8A3R8R2A1S38Vsegs;S3cVsegs;R8S5eR4A1M1R3A4S36S30S7fVsegs;R9S47S5dS78S60RaA1RcA4S61R5R4A2R1A5R8R1A1A2Lw;A3F_;F_;Frho;FE;S5dS1S32S5dR2RaA3R9R2A1S38Vsegs;S3cVsegs;R9G1R3A4R8A3F_;F_;Frho;Fn;F_;F_;F_;FQ;FK;FG;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits G K Q HG Hchk Hexits n rho Hin Hg.
  unfold check_ecfg in Hchk. apply andb_prop in Hchk as [Hstrict Hchk].
  destruct (cfg_edges segs fuel cutpcs g (map vn_state cuts) (map vn_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (vn_state n) with (en_state (to_enode G n)).
  apply (cfg_complete_gen segs fuel cutpcs g (map (to_enode G) cuts) (map (to_enode G) exits) es K Q).
  - apply forallb_forall. intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0).
    exact (proj1 (forallb_forall _ _) Hstrict m0 Hm0).
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeck_sound g G); [exact HG|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E rhoE HinE HgE. apply in_map_iff in HinE as (E0 & <- & HinE0).
    exact (Hexits E0 rhoE HinE0 HgE).
  - apply in_map_iff. exists n. auto.
  - exact Hg.
Qed.

Lemma eexit_post : ltac2:(tb__ "0|0|
S1bS71A1S72OF_;F_;S45S1S1bS5dA1S1bS93A1S5dS32S93S96S5eR1A1S94A2R2A3S1S4R7R6R1A3S38Vsegs;S3cVsegs;R9S5eR4A1R2A4S36S30S7fVsegs;RaS47S5dS78S60S1S4RaR9R1A3Lr;A1R7A4S61R5R3A2R1A5S43Vsegs;RaR9R8R6R1A6A2Lw;A3F_;Frho;F_;FP;Fposts;Fcuts;Frho0;Fn;FK;").
Proof using .
  intros K n rho0 cuts posts P Hin rho Hag w [Hsm Hk]. exists w. split; [apply wsteps_refl|].
  right. exists (mkLeaf (vn_state P) RsSymJump), rho. auto.
Qed.

Lemma eexit_reenter : ltac2:(tb__ "0|1|
S1bS71A1S72OF_;F_;S1OF_;S45S1bS5dA1S36OF_;S5dS5dS1bS2A1S0S9bS32S5dR4R7A3S2dS0S5eR5A1S76R4R3A2A3S2dS1cSafS5eR7A1R4R3A3S1dA3S2dS1cS9dR4RbA2S1dA3S1S1RfR2A1S4RfR3R2A3R11R3A1F_;F_;Frho';Frho;S2dS1cS33S2S9S6R7A1A1R8A3S1dA3S1S48S2S5R1A1S7S5eRcA1A1A3S48S2S5S9cR2R9A2A1RbA3F_;Frho;Sa5Sa8S5fRbA1Z1A2S5fRcA1M0A2Sa5Z0G0A2S1R13R1A1S38Vsegs;S3cVsegs;R15S5eR10A1R2A4S36S30S7fVsegs;R16S47S5dS78S60R15A1R13A4S61R11R3A2R1A5R12R1A1A2Lw;A3F_;Frho;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fs;FT0;FF;FC;FE;FQ;Fcuts;Fg;FG;FK;").
Proof using .
  intros K G g cuts Q E C F T0 s Hin HC He Hid HG Hb HF Hrk Hr0 rho Hg w Hsp.
  exists w. split; [apply wsteps_refl|]. left.
  exists (to_enode G C), (rho_sub rho s). split; [apply in_map; exact Hin|].
  cbn [to_enode en_state en_ghost en_meas fst snd]. split.
  - eapply HG; [exact Hg|]. apply rho_sub_agree. exact Hid.
  - split.
    + rewrite HC. eapply SP_entails_sem; eauto.
    + unfold vmeas.
      pose proof (urange (eval (rho_sub rho s) (vn_var C))) as R1.
      pose proof (urange (eval rho (vn_var E))) as R2. nia.
Qed.

End ECfgAuto.

Section ECfgLex.
Variable segs : list Segment.

Inductive vdir := Vdown (sgn : bool) | Vup (sgn : bool).
Definition vd_signed (d : vdir) : bool := match d with Vdown b | Vup b => b end.

Record lnode := mkLN { ln_state : sstate; ln_rank : Z; ln_vars : list (vdir * sv) }.

Definition LMAX : nat := 4%nat.
Definition B64 : Z := 2 ^ 64.

Definition base_val (rho : valuation) (sgn : bool) (e : sv) : Z := ltac2:(tb__ "0|2|
S1cS46Lsgn;Vsgn;Sa8ScfQ40M0S14Vrho;Ve;A2M1A2Sa7Z2Z3fA2A2SceG0G1A2X1cx2").

Definition comp_val (rho : valuation) (c : vdir * sv) : Z := ltac2:(tb__ "0|1|
S49S46Lx;S25S49S3Vc;A3S1cS51Vrho;R1S28S49S3Vc;A3A3M0Lsgn;S1cSaeSaeS4cZ1A2G0A2Lsgn;X49x2").

Fixpoint lex_val (rho : valuation) (l : list (vdir * sv)) : Z :=
  match l with
  | [] => 0
  | c :: t => comp_val rho c * B64 ^ Z.of_nat (length t) + lex_val rho t
  end.

Definition lmeas (n : lnode) (rho : valuation) : Z := ltac2:(tb__ "0|1|
Sa8SaaS52Vn;A1Sa7S4cSa9S4dA1A2A2SaaS4eVrho;S55Vn;A1M0A2Sa7S4cSa9Sc4S4dS27S20S49S3A2G0A2A2A1A2A2A2").

Definition to_enodeL (G : valuation -> Prop) (n : lnode) : enode := ltac2:(tb__ "0|1|
S21S20S0S1OF_;M0A2S1S46Frho;S21S0G0S4bVn;A1VG;A4S54Vn;A1A4").

Definition xleq (facts : list sprop) (sgn : bool) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S1cS1cLsgn;Vsgn;S9aVfacts;Va;Vk;Vb;A4S99Vfacts;Va;Vk;Vb;A4X1cx2").

Definition xlt (facts : list sprop) (d : vdir) (tgt src : sv) : bool := ltac2:(tb__ "0|1|
S49S1cLd;Vd;S1cS50Vfacts;R1Vtgt;Z1M0Vsrc;A5Lsgn;S1cS50Vfacts;R1Vsrc;G0Vtgt;A5Lsgn;X49x2").
Definition xle (facts : list sprop) (d : vdir) (tgt src : sv) : bool := ltac2:(tb__ "0|1|
S2aS1aVtgt;Vsrc;A2S49S1cLd;Vd;S1cS50Vfacts;R1Vtgt;Z0M0Vsrc;A5Lsgn;S1cS50Vfacts;R1Vsrc;G0Vtgt;A5Lsgn;X49x2A2").

Definition vdir_eqb (a b : vdir) : bool := ltac2:(tb__ "0|3|
S49S1cLa;Va;S1cS49S1cLb;M0Vb;S1cSd3R2R1A2Ly;M1S1cS26Lsgn;M2X49x2Lx;S1cG0Vb;G2G1X49x2Lx;X49x2").

Fixpoint lex_check (facts : list sprop) (s : wsub) (tgt src : list (vdir * sv)) : bool :=
  match tgt, src with
  | (dt, et) :: trest, (ds, es) :: srest =>
      vdir_eqb dt ds
      && (xlt facts ds (sv_subst s et) es
          || (xle facts ds (sv_subst s et) es && lex_check facts s trest srest))
  | _, _ => false
  end.

Definition echeck2 (g : positive) (nodes : list lnode) (e : edge) : bool := ltac2:(tb__ "0|9|
S1eS4aA1S1cLx;M0S34S4aVnodes;S7bVe;A1A3S4aG0S34S4aVnodes;S7dVe;A1A3S4aS23S23S23S23S23S23S9dS7cVe;A1M1Vg;A2Sc7Vg;S6S4bR2A1A1A2A2S33S20S49S3A2M2G2S13S6S4bR3A1A1S28S49S3R1A3A2Lc;S55R2A1M3A3A2SccS27G2G3A2M4S4dA2A2SccS27G2S55R1A1M5A2M6S4dA2A2SacZ0S52R1A1M7A2A2S2aSadG7S52R2A1M8A2S23S23SabG7G8A2ScdG6G4A2A2S57S7S7aVe;A1A1G1G5G3A4A2A2A2Lnj;S26X1ex2Lni;S26X1ex2").

Definition check_ecfg2 (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list lnode) : bool := ltac2:(tb__ "0|1|
S23S33S4aS4aS29S8S4bR1A1A1A1Ln;Vcuts;A3S1eS1bS73A1M0A1S1cLx;S75Vsegs;Vfuel;Vcutpcs;Vg;S47S4aS0S4bVcuts;A4S47S4aS0S4bVexits;A4A6G0S33S73S53Vg;S24S4aVcuts;Vexits;A3A2R1A3Les;S26X1ex2A2").

Lemma B64_pos : ltac2:(tb__ "0|0|
S1fSa6Z0Sa7S4cSa9R1A1A2A2Fk;").
Proof using . intros k. unfold B64. apply Z.pow_pos_nonneg; lia. Qed.

Lemma base_val_range : ltac2:(tb__ "0|1|
S1S1cS3S2eSa5Z0S51R3R2R1A3M0A2Sa6G0S4cA2A2Fe;Fsgn;Frho;").
Proof using .
  intros rho sgn e. unfold base_val, B64.
  pose proof (urange (eval rho e)) as R.
  destruct sgn.
  - pose proof (bv_signed_in_range 64 (eval rho e) ltac:(discriminate)) as S.
    change (bv_half_modulus 64) with (2 ^ 63) in S. lia.
  - lia.
Qed.

Lemma comp_val_range : ltac2:(tb__ "0|1|
S1S20S49S3A2S2eSa5Z0S4fR2R1A2M0A2Sa6G0S4cA2A2Fc;Frho;").
Proof using .
  intros rho [d e]. unfold comp_val. cbn [fst snd].
  pose proof (base_val_range rho (vd_signed d) e) as R.
  destruct d as [sgn|sgn]; cbn [vd_signed] in R; lia.
Qed.

Lemma lex_val_range : ltac2:(tb__ "0|2|
S1S1bS20S49S3A2M0A1S2eSa5Z0S4eR2R1A2M1A2Sa6G1Sa7S4cSa9S27G0R1A2A1A2A2A2Fl;Frho;").
Proof using .
  intros rho l. induction l as [|c t IH]; cbn [lex_val length].
  - cbn. lia.
  - pose proof (comp_val_range rho c) as C. pose proof (B64_pos (length t)) as P.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma xleq_sound : ltac2:(tb__ "0|0|
S1S1bS2A1S1cS3S46S3S48S2S5R6A1R5A3S2dS1cS50R6R5R4R3R2A5S1dA3Sa5Sa8S51R8R6R5A3R4A2S51R8R6R3A3A2F_;F_;Fb;Fk;Fa;Fsgn;Ffacts;Frho;").
Proof using .
  intros rho facts sgn a k b Hf H. unfold xleq in H. unfold base_val. destruct sgn.
  - pose proof (sleq_sound rho facts a k b Hf H) as S. unfold soff in S. lia.
  - pose proof (uleq_sound rho facts a k b Hf H) as S. unfold U in S. lia.
Qed.

Lemma xlt_sound : ltac2:(tb__ "0|0|
S1S1bS2A1S49S3S3S48S2S5R5A1R4A3S2dS1cS5cR5R4R3R2A4S1dA3Sa5Sa8S4fR7S21S49S3R5R4A4A2Z1A2S4fR7S21S49S3R5R3A4A2A2F_;F_;Fb;Fa;Fd;Ffacts;Frho;").
Proof using .
  intros rho facts d a b Hf H. unfold xlt in H. unfold comp_val. cbn [fst snd].
  destruct d as [sgn|sgn]; pose proof (xleq_sound rho facts sgn _ _ _ Hf H); lia.
Qed.

Lemma xle_sound : ltac2:(tb__ "0|0|
S1S1bS2A1S49S3S3S48S2S5R5A1R4A3S2dS1cS5bR5R4R3R2A4S1dA3Sa5S4fR7S21S49S3R5R4A4A2S4fR7S21S49S3R5R3A4A2A2F_;F_;Fb;Fa;Fd;Ffacts;Frho;").
Proof using .
  intros rho facts d a b Hf H. unfold xle in H. apply orb_prop in H as [H|H].
  - rewrite (sv_eqb_sound _ _ H). lia.
  - unfold comp_val. cbn [fst snd].
    destruct d as [sgn|sgn]; pose proof (xleq_sound rho facts sgn _ _ _ Hf H); lia.
Qed.

Lemma vdir_eqb_sound : ltac2:(tb__ "0|0|
S49S49S2dS1cS5aR2R1A2S1dA3S2dS49R3R2A3F_;Fb;Fa;").
Proof using . intros [x|x] [y|y] H; cbn in H; try discriminate; apply Bool.eqb_prop in H; congruence. Qed.

Lemma lex_check_sound : ltac2:(tb__ "0|2|
S1S1bS2A1S9bS1bS20S49S3A2M0A1M1G1S48S2S5R5A1R4A3S2dS1cS57R5R4R3R2A4S1dA3S2dS1fS27G0R4A2S27G0R3A2A3Sa6S4eS9cR8R6A2R5A2S4eR8R4A2A2F_;F_;F_;Fsrc;Ftgt;Fs;Ffacts;Frho;").
Proof using .
  intros rho facts s tgt. induction tgt as [|[bt et] trest IH]; intros src Hf H Hlen; [discriminate|].
  destruct src as [|[bs es] ts]; [discriminate|]. cbn [lex_check] in H.
  apply andb_prop in H as [Hb H]. apply vdir_eqb_sound in Hb. subst bt.
  cbn [lex_val length]. cbn in Hlen. apply Nat.succ_inj in Hlen.
  assert (CE : comp_val (rho_sub rho s) (bs, et) = comp_val rho (bs, sv_subst s et)).
  { unfold comp_val, base_val. cbn [fst snd]. rewrite !eval_subst. reflexivity. }
  rewrite CE, Hlen.
  pose proof (lex_val_range (rho_sub rho s) trest) as Rt. pose proof (lex_val_range rho ts) as Rs. rewrite Hlen in Rt.
  pose proof (B64_pos (length ts)) as P.
  apply orb_prop in H as [H|H].
  - pose proof (xlt_sound rho facts bs _ _ Hf H) as X. nia.
  - apply andb_prop in H as [H1 H2]. pose proof (xle_sound rho facts bs _ _ Hf H1) as X.
    pose proof (IH ts Hf H2 Hlen) as R. nia.
Qed.

Lemma lex_val_agree : ltac2:(tb__ "0|1|
S45S1S1S1bS20S49S3A2M0A1S4R4R3R2A3S2dS1cS33G0G0S13R6S28S49S3R1A3A2Lc;R2A3S1dA3S2dS46S4eR5R3A2S4eR4R3A2A3F_;F_;Fl;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' l Hag H. induction l as [|[b e] t IH]; cbn [lex_val]; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2].
  unfold comp_val, base_val. cbn [fst snd]. rewrite (eval_agree n rho rho' e Hag H1). rewrite IH by exact H2. reflexivity.
Qed.

Lemma lmeas_nonneg : ltac2:(tb__ "0|1|
S4aS1Sa5Z0M0S52R2A1A2Sa5G0S54R3R2A2A2F_;Frho;Fn;").
Proof using .
  intros n rho H. unfold lmeas. pose proof (lex_val_range rho (ln_vars n)).
  pose proof (B64_pos LMAX). pose proof (B64_pos (LMAX - length (ln_vars n))). nia.
Qed.

Lemma lex_part_bound : ltac2:(tb__ "0|1|
S1S1bS20S49S3A2M0A1ScbS27G0R1A2S4dA2Sa6SaaS4eR3R2A2Sa7S4cSa9Sc4S4dS27G0R2A2A2A1A2A2Sa7S4cSa9S4dA1A2A2F_;Fl;Frho;").
Proof using .
  intros rho l Hl. pose proof (lex_val_range rho l) as R. pose proof (B64_pos (LMAX - length l)) as P.
  replace (B64 ^ Z.of_nat LMAX) with (B64 ^ Z.of_nat (length l) * B64 ^ Z.of_nat (LMAX - length l)).
  - nia.
  - rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma echeck2_sound : ltac2:(tb__ "0|0|
S45S1OF_;S1bS4aA1S73S1S1R5R2A1S4R7R3R2A3R7R3A1F_;F_;Fr2;Fr1;S2dS1cS53R5R3R2A3S1dA3S87S47S4aS78S58R5A1R4A4R3A2F_;F_;Fe;Fnodes;FG;Fg;").
Proof using .
  intros g G nodes e HG H. unfold echeck2 in H. unfold eedge_ok.
  intros Ti Tj Hi Hj rho rho' Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enodeL en_state en_ghost en_meas fst snd] in *.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H Hrk].
  apply andb_prop in H as [H Hlj]. apply andb_prop in H as [H Hli].
  apply andb_prop in H as [H Hvb]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle. apply Z.leb_le in Hrk. apply Nat.leb_le in Hli. apply Nat.leb_le in Hlj.
  split.
  - eapply HG; [exact Hg|]. eapply agree_below_trans.
    + eapply agree_below_le; [exact Hgle | exact Hag].
    + apply rho_sub_agree. exact Hid.
  - split; [apply lmeas_nonneg; exact Hrk|].
    unfold lmeas.
    pose proof (lex_part_bound (rho_sub rho' (e_sub e)) (ln_vars nj) Hlj) as Bj.
    pose proof (lex_val_range rho (ln_vars ni)) as Ri.
    pose proof (B64_pos (LMAX - length (ln_vars ni))) as Pi. pose proof (B64_pos LMAX) as PL.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + apply Z.ltb_lt in Hlt. nia.
    + apply andb_prop in Heq as [Heq Hlex]. apply andb_prop in Heq as [Heq Hlen].
      apply Z.eqb_eq in Heq. apply Nat.eqb_eq in Hlen.
      pose proof (lex_check_sound rho' _ _ _ _ HF Hlex Hlen) as L.
      rewrite <- (lex_val_agree _ rho rho' (ln_vars ni) Hag Hvb) in L.
      rewrite Heq, Hlen. nia.
Qed.

Theorem cfg_complete_auto2 : ltac2:(tb__ "0|2|
S1fS1bS46A1S45S1bS4aA1M0G0S1OF_;S1bS71A1S72OF_;F_;S36OF_;S1S1R5R2A1S4R9R3R2A3R7R3A1F_;F_;Fr2;Fr1;S2dS1cS56R9R8R7R6R5A5S1dA3S4aS1S32S4aR2R8A3R8R2A1S38Vsegs;S3cVsegs;R8S4bR4A1M1R3A4S36S30S7fVsegs;R9S47S4aS78S58RaA1RcA4S54R5R4A2R1A5R8R1A1A2Lw;A3F_;F_;Frho;FE;S4aS1S32S4aR2RaA3R9R2A1S38Vsegs;S3cVsegs;R9G1R3A4R8A3F_;F_;Frho;Fn;F_;F_;F_;FQ;FK;FG;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits G K Q HG Hchk Hexits n rho Hin Hg.
  unfold check_ecfg2 in Hchk. apply andb_prop in Hchk as [Hstrict Hchk].
  destruct (cfg_edges segs fuel cutpcs g (map ln_state cuts) (map ln_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (ln_state n) with (en_state (to_enodeL G n)).
  apply (cfg_complete_gen segs fuel cutpcs g (map (to_enodeL G) cuts) (map (to_enodeL G) exits) es K Q).
  - apply forallb_forall. intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0).
    exact (proj1 (forallb_forall _ _) Hstrict m0 Hm0).
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeck2_sound g G); [exact HG|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E rhoE HinE HgE. apply in_map_iff in HinE as (E0 & <- & HinE0).
    exact (Hexits E0 rhoE HinE0 HgE).
  - apply in_map_iff. exists n. auto.
  - exact Hg.
Qed.

Definition to_gnodeL (G : valuation -> Prop) (n : lnode) : gnode := ltac2:(tb__ "0|0|
S21S0S1OF_;S4bVn;A1VG;A4").

Lemma echeck2_edge_ok : ltac2:(tb__ "0|0|
S45S1OF_;S1bS4aA1S73S1S1R5R2A1S4R7R3R2A3R7R3A1F_;F_;Fr2;Fr1;S2dS1cS53R5R3R2A3S1dA3S83S47S4aS7eS59R5A1R4A4R3A2F_;F_;Fe;Fnodes;FG;Fg;").
Proof using .
  intros g G nodes e HG H. unfold echeck2 in H. unfold edge_ok.
  intros Ti Tj Hi Hj rho rho' Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_gnodeL fst snd] in *.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle.
  eapply HG; [exact Hg|]. eapply agree_below_trans.
  - eapply agree_below_le; [exact Hgle | exact Hag].
  - apply rho_sub_agree. exact Hid.
Qed.

Theorem cfg_sound_auto2 : ltac2:(tb__ "0|2|
S1fS1bS46A1S45S1bS4aA1M0G0S1OF_;S36OF_;S1bS71A1S72OF_;F_;S39S3fVsegs;R3R2A3S1S1R7R2A1S4RbR3R2A3R9R3A1F_;F_;Fr2;Fr1;S2dS1cS56RbRaR9R8R7A5S1dA3S4aS1S32S4aR2RaA3RaR2A1S37Vsegs;RaS3cVsegs;R9S4bR4A1M1R3A4S36S30S82Vsegs;RaRcS47S4aS0S4bReA4R1A5R9R1A1A2Lw;A4F_;F_;Frho;FE;S4aS1S32S4aR2RcA3RbR2A1S37Vsegs;RbS3cVsegs;RaG1R3A4R9A4F_;F_;Frho;Fn;F_;F_;F_;F_;FQ;FK;Fok;FG;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits G ok K Q Hok HG Hchk Hexits n rho Hin Hg.
  unfold check_ecfg2 in Hchk. apply andb_prop in Hchk as [Hstrict Hchk].
  destruct (cfg_edges segs fuel cutpcs g (map ln_state cuts) (map ln_state exits)) as [es|] eqn:Hes; [|discriminate].
  refine (cfg_sound_gen segs fuel cutpcs g (map (to_gnodeL G) cuts) (map (to_gnodeL G) exits) es ok K Q Hok _ _ _ _ (ln_state n) G rho _ Hg).
  - intros Hl. exfalso. apply existsb_exists in Hl as (TG & HinTG & HlTG).
    apply in_map_iff in HinTG as (m & <- & Hm). cbn [to_gnodeL fst] in HlTG.
    pose proof (proj1 (forallb_forall _ _) Hstrict m Hm) as X. cbn beta in X. rewrite HlTG in X. discriminate.
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeck2_edge_ok g G); [exact HG|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E GE rhoE HinE HgE. apply in_map_iff in HinE as (E0 & Heq & HinE0).
    unfold to_gnodeL in Heq. injection Heq as <- <-.
    eapply triple_conseq; [intros w Hw; exact Hw | | exact (Hexits E0 rhoE HinE0 HgE)].
    intros w [Hw|Hw]; [left | right; exact Hw].
    destruct Hw as (T & rho1 & HinT & Hg1 & Hsp1). apply in_map_iff in HinT as (n1 & <- & Hn1).
    exists (ln_state n1), G, rho1. split; [|auto]. apply in_map_iff. exists n1. split; [reflexivity | exact Hn1].
  - apply in_map_iff. exists n. auto.
Qed.

End ECfgLex.

Section WithSegsR.
Variable segs : list Segment.

Definition nodes_at (ok : assn) (K : list event -> Model -> Prop) (nodes : list gnode)
           (Q : assn) (m : nat) : Prop := ltac2:(tb__ "0|1|
S0S1OF_;M0S1S32S20S0G0A2S21S0G0R3R2A4Vnodes;A3R3R2A1S3aVsegs;Vok;Vm;S3cVsegs;VK;R5R3A4VQ;A5F_;F_;Frho;FG;FT;").

Theorem cfg_sound_rec : ltac2:(tb__ "0|5|
S1fS1bS46A1S45S1bS7eA1M0G0S1bS73A1M1S36OF_;S1bS71A1S72OF_;F_;S39S3fVsegs;R3R2A3S2dS1cS35S20S0S1OF_;M2A2M3G3S8S25S0G2R1A3A1LTG;R7A3S1dA3S40Vsegs;R5R4A3F_;S2dS1eG1A1S75Vsegs;RbRaR9S47G3S0S25S0G2A2M4R8A4S47G3S0G4R7A4A6S22G1R6A2A3S48S73S83S24S7eR9R8A3A1R7A3S1fS0G2S1S32G3S21S0G2R3R2A4RdA3R3R2A1Sc6RdRcR10RbR6A5S3aVsegs;ReR7S3cVsegs;RdR6R4A4RcA5F_;F_;F_;Frho;FGE;FE;Fm;S1fSc6R9R8RcR7R1A5Fn;F_;F_;F_;F_;F_;FQ;FK;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok K Q Hok Hokf Hes Hedges Hexits n.
  induction n as [|n IH]; intros T G rho HinT Hg.
  - intros _ w _. exact I.
  - destruct (In_nth_error _ _ HinT) as [k Hk].
    assert (HkT : nth_error (map fst cuts) k = Some T) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edges in Hes.
    destruct (cuts_edges_spec segs fuel cutpcs g (map fst cuts) 0 (map fst cuts ++ map fst exits) es Hes k T HkT)
      as (Hle & leaves & Hrun & HL).

    intros HgQS. pose proof (@guards_mono segs ok (S n) n Q ltac:(lia) HgQS) as HgQ.
    apply (sym_run_sound segs fuel cutpcs T leaves ok K rho Hrun Hok
             ltac:(intros Hlen; apply Hokf; apply existsb_exists; exists (T, G); split; [exact HinT|exact Hlen]) n).
    intros w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent). rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold edge_ok in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold gnode in *.
    destruct (nth_error (cuts ++ exits) j) as [[Xs GX]|] eqn:HnXG; cbn in HnX; [|discriminate].
    injection HnX as ->.
    assert (HGX : GX (rho_sub rho'' s)).
    { eapply (EOK (T, G) (X, GX)); [| reflexivity | exact Hag | exact Hg |].
      - rewrite nth_error_app1; [exact Hk|]. apply nth_error_Some. congruence.
      - destruct w as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
    pose proof (SP_entails segs K (lf_state L) X s rho'' w Hent (conj Hsm Hkk)) as HSPX.
    destruct (Nat.lt_ge_cases j (length cuts)) as [Hj|Hj].
    + rewrite nth_error_app1 in HnXG by exact Hj.
      exact (IH X GX (rho_sub rho'' s) (nth_error_In _ _ HnXG) HGX HgQ w HSPX).
    + rewrite nth_error_app2 in HnXG by exact Hj.
      exact (Hexits n X GX (rho_sub rho'' s) (nth_error_In _ _ HnXG) HGX IH HgQ w HSPX).
Qed.

Corollary cfg_sound_rec_triple : ltac2:(tb__ "0|7|
S1fS1bS46A1S45S1bS7eA1M0G0S1bS73A1M1S36OF_;S1bS71A1S72OF_;F_;S39S3fVsegs;R3R2A3S2dS1cS35S20S0S1OF_;M2A2M3G3S8S25S0G2R1A3A1LTG;R7A3S1dA3S40Vsegs;R5R4A3F_;S2dS1eG1A1S75Vsegs;RbRaR9S47G3S0S25S0G2A2M4R8A4S47G3S0G4R7A4A6S22G1R6A2A3S48S73S83S24S7eR9R8A3A1R7A3S1fS0G2S1S32G3S21S0G2R3R2A4M5RdA3R3R2A1M6Sc6RdRcR10RbR6A5S3aVsegs;ReR7S3cVsegs;RdR6R4A4RcA5F_;F_;F_;Frho;FGE;FE;Fm;S0G2S1S32G3G5ReA3G6S37Vsegs;RdS3cVsegs;RcR5R3A4RbA4F_;F_;Frho;FG;FT;F_;F_;F_;F_;F_;FQ;FK;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok K Q Hok Hokf Hes Hedges Hexits T G rho HinT Hg n.
  exact (cfg_sound_rec fuel cutpcs g cuts exits es ok K Q Hok Hokf Hes Hedges Hexits n T G rho HinT Hg).
Qed.

End WithSegsR.

Definition withG (G : valuation -> Prop) (J : jpred) : jpred := ltac2:(tb__ "0|0|
S1S1bS71A1S72S2eVG;R3A1VJ;R3R2R1A3A2Lmd;Ltr;Lrho;").

Lemma stableJ_withG : ltac2:(tb__ "0|0|
S45S1OFx;S3bS1S1R4R2A1S4R6R3R2A3R6R3A1F_;F_;Frho';Frho;S3eR4R2A2S3eR5S79R4R3A2A2F_;F_;FJ;FG;Fn;").
Proof.
  intros n G J HG HJ rho rho' tr md Hag [Hg Hj]. split; [eapply HG; eauto | eapply HJ; eauto].
Qed.

Lemma stableJ_agree : ltac2:(tb__ "0|0|
S45S1S1S1S4R4R3R2A3S4R5R3R2A3S4R6R5R3A3F_;F_;Frho';Frho;Frho0;Fn;").
Proof. intros n rho0 rho rho' H1 H2. eapply agree_below_trans; eauto. Qed.

Section CFGJ.
Variable segs : list Segment.

Definition SPfamJ (J : jpred) (fam : list sstate) : assn := ltac2:(tb__ "0|0|
S36S2fS0S0S2fS1S1S2eS32S0R2Vfam;A3S3dVsegs;VJ;R2R1R3A5A2Lrho;A2LT;A2Lw;").

Lemma SPfamJ_app : ltac2:(tb__ "0|1|
S3bS1bS0A1M0G0S36S31S67R4S24S0R3R2A3R1A3S30S67R4R3R1A3S67R4R2R1A3A2A2Fw;Ff2;Ff1;FJ;").
Proof using .
  intros J f1 f2 w. unfold SPfamJ. split.
  - intros (T & rho & Hin & Hsp). apply in_app_or in Hin as [Hin|Hin];
      [left|right]; exists T, rho; auto.
  - intros [(T & rho & Hin & Hsp)|(T & rho & Hin & Hsp)];
      exists T, rho; (split; [apply in_or_app; auto|auto]).
Qed.

Lemma leaf_matches_soundJ : ltac2:(tb__ "0|0|
S3bS45S0S1bS0A1S1S36S3eR5R6A2S2dS1cS90R6R5R4A3S1dA3S3dVsegs;R8R6R4R3A5S67R9R6R4A3F_;F_;F_;Fw;Frho;Ftargets;FL;Fg;FJ;").
Proof using .
  intros J g L targets rho w HJ Hm Hsp.
  unfold leaf_matches in Hm. rewrite existsb_lazy_eq in Hm. apply existsb_exists in Hm as (X & Hin & Hm).
  apply leaf_matches1_true in Hm as [Hid He].
  exists X, (rho_sub rho (infer_sub g L X)). split; [exact Hin|].
  eapply SPJ_entails; eauto.
Qed.

Theorem cfg_soundJ : ltac2:(tb__ "0|1|
S1fS1bS46A1S45S1bS0A1M0G0S3bS36OF_;S39S42Vsegs;R2R3A3S2dS1cS35S0S8R6A3S1dA3S41Vsegs;R4R5A3F_;S3eR8R5A2S2dS1cS8dVsegs;RbRaR9R8R7A6S1dA3S0S1S32S0R2RaA3S37Vsegs;R9S3dVsegs;RaR3R2A4S36S30S67RbRdR1A3R9R1A1A2Lw;A4F_;Frho;FE;S0S1S32S0R2RcA3S37Vsegs;RaS3dVsegs;RbR3R2A4R9A4F_;Frho;FT;F_;F_;F_;F_;F_;FQ;Fok;FJ;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits J ok Q Hok Hokf HJ Hchk Hexits T rho HinT.
  assert (Hloop : triple segs ok (SPfamJ J cuts) Q).
  { apply triple_loop.
    unfold SPfamJ at 1. apply triple1_ex; intros T'. apply triple1_ex; intros rho'.
    apply triple1_pure; intros HinT'.
    unfold check_cfg in Hchk. rewrite forallb_lazy_eq in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk T' HinT') as Hc.
    unfold check_cut in Hc. destruct (Pos.leb g (ss_next T')) eqn:Hle; [|discriminate]. apply Pos.leb_le in Hle.
    destruct (sym_run segs fuel cutpcs T' true) as [leaves|] eqn:Hrun; [|discriminate]. rewrite forallb_lazy_eq in Hc.
    eapply triple1_seq_l.
    { eapply sym_run_soundJ; eauto; [|eapply stableJ_mono; [exact Hle|exact HJ]].
      intros Hlen. apply Hokf. apply existsb_exists. exists T'. auto. }
    intros m Hgm w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hk).
    pose proof (proj1 (forallb_forall _ _) Hc L HinL) as HmL.
    pose proof (leaf_matches_soundJ J g (lf_state L) (cuts ++ exits) rho'' w HJ HmL (conj Hsm Hk)) as Hfam.
    apply SPfamJ_app in Hfam as [Hcut|Hexit].
    - exact (Hgm w (or_introl Hcut)).
    - destruct Hexit as (E & rhoE & HinE & HspE).
      exact (Hexits E rhoE HinE m Hgm w HspE). }
  eapply triple_conseq; [| intros w Hw; exact Hw | exact Hloop].
  intros w Hw. exists T, rho. auto.
Qed.

Lemma SPJ_entails_sem : ltac2:(tb__ "0|0|
S3bS45S0S0S1bS2A1S9bS1S36S2dS1cSafR6R5R3A3S1dA3S2dS1cS9dR4R8A2S1dA3S3eR9RaA2S2dS1cS33S2S9S6R8A1A1R7A3S1dA3S1S1bS71A1S72RfR3R2R1A3S48S2S5R4A1S7ReA1A3S48S2S5S9cR5RcA2A1RdA3F_;F_;Fmd;Ftr;Frho;S3dVsegs;RdRbR7R6A5S3dVsegs;ReS76RaRbA2S9cR8R9A2R7A5F_;F_;F_;F_;F_;F_;Fw;Frho;Fs;FF;FT0;FL;Fg;FJ;").
Proof using .
  intros J g L T0 F s rho w He Hid HJ Hb HF [Hsm Hk]. split; [|eapply HJ; [apply rho_sub_agree; exact Hid | exact Hk]].
  apply smatch_add_facts; [eapply entails_sound; eauto | | exact Hb].
  eapply HF; [exact Hk|]. destruct w as [tr [ms md]].
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma exit_reenterJ : ltac2:(tb__ "0|0|
S36OF_;S3bS45S1bS0A1S39S0S0S1bS2A1S9bS32S0S76R2R3A2R6A3S2dS1cSafR5R4R2A3S1dA3S2dS1cS9dR3R9A2S1dA3S3eRaRbA2S2dS1cS33S2S9S6R7A1A1R6A3S1dA3S1S1bS71A1S72R10R3R2R1A3S48S2S5R4A1S7RdA1A3S48S2S5S9cR5RbA2A1RcA3F_;F_;Fmd;Ftr;Frho;S1S37Vsegs;R10S3dVsegs;RfRbR1A4S36S30S67R10ReR1A3RdR1A1A2Lw;A4Frho;F_;F_;F_;F_;F_;F_;Fs;FF;FT0;FE;FQ;Fcuts;Fg;FJ;Fok;").
Proof using .
  intros ok J g cuts Q E T0 F s Hin He Hid HJ Hb HF rho.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hsp. left. exists (add_facts F T0), (rho_sub rho s).
  split; [exact Hin|]. eapply SPJ_entails_sem; eauto.
Qed.

Lemma exit_postJ : ltac2:(tb__ "0|0|
S36OF_;S3bS45S1S1bS0A1S1bS93A1S0S32S93S96R1S94A2R2A3S1S37Vsegs;R9S3dVsegs;S79S1S4R8R7R1A3Lr;R8A2R3R1A4S36S30S67S79S1S4R9R8R1A3Lr;R9A2R6R1A3S44Vsegs;R9R8R7R5R1A6A2Lw;A4Frho;F_;FP;Fposts;Fcuts;Frho0;Fn;FJ0;Fok;").
Proof using .
  intros ok J0 n rho0 cuts posts P Hin rho.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w [Hsm [Hag Hk]]. right. exists (mkLeaf P RsSymJump), rho. auto.
Qed.

Lemma SPJ_withG_intro : ltac2:(tb__ "0|0|
S3bS45S0S1S36S3dVsegs;R5R3R2R1A5S3dVsegs;S79S1S4R6R4R1A3Lr;R6A2R4R3R2A5F_;Fw;Frho;FS;Fn;FJ0;").
Proof using . intros J0 n S rho w [Hsm Hk]. split; [exact Hsm|]. split; [apply agree_below_refl | exact Hk]. Qed.

Definition jnode : Type := (sstate * jpred)%type.

Definition edge_okJ (nodes : list jnode) (e : edge) : Prop := ltac2:(tb__ "0|2|
S66S66S2dS1eS66A1M0S34S66Vnodes;S7bVe;A1A3S22S66R2A2M1A3S2dG0S34S66Vnodes;S7dVe;A1A3G1A3S1S1S1bS71A1S72S4S6S25S0S3bR8A3A1R4R3A3S28S0S3bR9R5R3R2A6S48S2S5R5A1S7S7aVe;A1A1A3S28S0S3bRaS9cR6S7cVe;A1A2R5R4A6F_;F_;F_;Fmd;Ftr;Frho';Frho;F_;F_;FTj;FTi;").

Definition SPfamGJ (nodes : list jnode) : assn := ltac2:(tb__ "0|0|
S36S2fS0S0S2fS3bS3bS2fS1S1S2eS32S20S0S3bA2S21S0S3bR3R2A4Vnodes;A3S3dVsegs;R2R3R1R4A5A2Lrho;A2LJ;A2LT;A2Lw;").

Theorem cfg_sound_genJ : ltac2:(tb__ "0|7|
S1fS1bS46A1S45S1bS66A1M0G0S1bS73A1M1S36OF_;S39S0S3bS32S20S0S3bA2M2S21S0S3bR2R1A4M3R7A3S42Vsegs;R5R2A3F_;FJ;FT;S0S3bS32G2G3R8A3S2dS1cS8R3A1S1dA3S41Vsegs;R7R3A3F_;F_;FJ;FT;S2dS1eG1A1S75Vsegs;RaR9R8S47G2S0S25S0S3bA2M4R7A4S47G2S0G4R6A4A6S22G1R5A2A3S48S73S6dS24S66R8R7A3A1R6A3S0S3bS1S32G2S21S0S3bR3R2A4M5RbA3S37Vsegs;RaS3dVsegs;R3R4R2A4M6S36S30S70ReR1A2RaR1A1A2Lw;A4F_;Frho;FJE;FE;S0S3bS1S32G2G5RdA3S37Vsegs;RbG6RaA4F_;Frho;FJ;FT;F_;F_;F_;F_;F_;FQ;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok Q Hok Hokf Hes Hedges Hexits T J rho HinT.
  assert (Hloop : triple segs ok (SPfamGJ cuts) Q).
  { apply triple_loop.
    unfold SPfamGJ at 1. apply triple1_ex; intros T'. apply triple1_ex; intros J'. apply triple1_ex; intros rho'.
    apply triple1_pure; intros HinT'.
    destruct (In_nth_error _ _ HinT') as [k Hk].
    assert (HkT : nth_error (map fst cuts) k = Some T') by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edges in Hes.
    destruct (cuts_edges_spec segs fuel cutpcs g (map fst cuts) 0 (map fst cuts ++ map fst exits) es Hes k T' HkT)
      as (Hle & leaves & Hrun & HL).
    eapply triple1_seq_l.
    {
      eapply (sym_run_sound segs fuel cutpcs T' leaves ok (J' rho') rho' Hrun).
      - intros tr ms md ms' Hk'. exact (Hok T' J' HinT' rho' tr ms md ms' Hk').
      - intros Hlen tr ms md Hk'. exact (Hokf T' J' HinT' Hlen rho' tr ms md Hk'). }
    intros m Hgm w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent).
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold edge_okJ in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold jnode in *.
    destruct (nth_error (cuts ++ exits) j) as [[Xs JX]|] eqn:HnXG; cbn in HnX; [|discriminate].
    injection HnX as ->.
    destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model liftK] in Hkk.
    assert (HJX : JX (rho_sub rho'' s) tr md).
    { eapply (EOK (T', J') (X, JX)); [| reflexivity | exact Hag | exact Hkk |].
      - rewrite nth_error_app1; [exact Hk|]. apply nth_error_Some. congruence.
      - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
    assert (HSPX : SPJ segs JX X (rho_sub rho'' s) (tr, mkCfg ms md)).
    { split; [eapply entails_sound; eauto | exact HJX]. }
    destruct (Nat.lt_ge_cases j (length cuts)) as [Hj|Hj].
    - apply Hgm. left. exists X, JX, (rho_sub rho'' s). split; [|exact HSPX].
      rewrite nth_error_app1 in HnXG by exact Hj. eapply nth_error_In; eauto.
    - rewrite nth_error_app2 in HnXG by exact Hj.
      exact (Hexits X JX (rho_sub rho'' s) (nth_error_In _ _ HnXG) m Hgm _ HSPX). }
  eapply triple_conseq; [| intros w Hw; exact Hw | exact Hloop].
  intros w Hw. exists T, J, rho. auto.
Qed.

Definition enodeJ : Type := ltac2:(tb__ "0|0|
S20S20S0S3bA2S1S46F_;A2").
Definition enj_state (n : enodeJ) : sstate := fst (fst n).
Definition enj_pred (n : enodeJ) : jpred := snd (fst n).
Definition enj_meas (n : enodeJ) : valuation -> Z := snd n.

Definition eedge_okJ (nodes : list enodeJ) (e : edge) : Prop := ltac2:(tb__ "0|4|
S65S65S2dS1eS65A1M0S34S65Vnodes;S7bVe;A1A3S22S65R2A2M1A3S2dG0S34S65Vnodes;S7dVe;A1A3G1A3S1S1S1bS71A1S72S4S6S68R8A1A1R4R3A3S6bR9R5R3R2A4S48S2S5R5A1S7S7aVe;A1A1A3S2eS6bRaS9cR6S7cVe;A1A2M2R5R4A4S2eSa5Z0S6aRaG2A2M3A2Sa6G3S6aRbR7A2A2A2A2F_;F_;F_;Fmd;Ftr;Frho';Frho;F_;F_;FTj;FTi;").

Definition SPfamEJ (nodes : list enodeJ) (bound : Z) : world -> Prop := ltac2:(tb__ "0|1|
S36S2fS65S65S2fS1S1S2eS32S65R2Vnodes;A3S2eS3dVsegs;S6bR2A1S68R2A1R1R3A5S2eSa5Z0S6aR2R1A2M0A2Sa6G0Vbound;A2A2A2A2Lrho;A2Ln;A2Lw;").

Theorem cfg_complete_genJ : ltac2:(tb__ "0|3|
S1fS1bS46A1S45S1bS65A1M0G0S1bS73A1M1S36OF_;S2dS1cS33S65S65S29S8S68R1A1A1A1Ln;R4A3S1dA3S2dS1eG1A1S75Vsegs;R8R7R6S47S65S0S68R5A4S47S65S0S68R4A4A6S22G1R3A2A3S48S73S6fS24S65R6R5A3A1R4A3S65S1S32S65R2R8A3S38Vsegs;S3dVsegs;S6bR3A1S68R3A1R2A4M2S36S30S69RbS6aR4R3A2R1A3R8R1A1A2Lw;A3F_;Frho;FE;S65S1S32S65R2RaA3S38Vsegs;G2R8A3F_;Frho;Fn;F_;F_;F_;F_;FQ;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es Q Hstrict Hes Hedges Hexits n rho Hin.
  set (I := fun (a : Z) (w : world) =>
              exists n rho, In n (cuts ++ exits) /\ SPJ segs (enj_pred n) (enj_state n) rho w /\ enj_meas n rho = a /\ 0 <= a).

  assert (ROUND : forall n0 rho0 w, In n0 cuts -> SPJ segs (enj_pred n0) (enj_state n0) rho0 w ->
            exists w' nj rhoj, wsteps segs w w' /\ In nj (cuts ++ exits)
              /\ SPJ segs (enj_pred nj) (enj_state nj) rhoj w'
              /\ 0 <= enj_meas nj rhoj < enj_meas n0 rho0).
  { intros n0 rho0 w Hcut Hsp0.
    destruct (In_nth_error _ _ Hcut) as [k Hk].
    assert (HkT : nth_error (map enj_state cuts) k = Some (enj_state n0)) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edges in Hes.
    destruct (cuts_edges_spec segs fuel cutpcs g (map enj_state cuts) 0 (map enj_state cuts ++ map enj_state exits) es Hes k _ HkT)
      as (Hle & leaves & Hrun & HL).
    assert (Hlen : ss_lenient (enj_state n0) = false).
    { pose proof (proj1 (forallb_forall _ _) Hstrict n0 Hcut) as X. cbn beta in X. destruct (ss_lenient (enj_state n0)); [cbn in X; discriminate|reflexivity]. }
    destruct (sym_run_etriple segs fuel cutpcs (enj_state n0) leaves (enj_pred n0 rho0) rho0 Hlen Hrun w Hsp0) as (w' & Hsteps & HLQ).
    destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent). rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_okJ in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold enodeJ in *.
    destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate]. injection HnX as HX.
    destruct w' as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model liftK] in Hkk.
    assert (FACTS : Forall (holds rho'') (ss_facts (lf_state L))).
    { exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
    destruct (EOK n0 nj ltac:(rewrite nth_error_app1; [exact Hk| apply nth_error_Some; congruence]) eq_refl rho0 rho'' tr md Hag Hkk FACTS) as [HGj HMj].
    exists (tr, mkCfg ms md), nj, (rho_sub rho'' s). split; [exact Hsteps|]. split; [eapply nth_error_In; exact HnXG|].
    split; [|exact HMj]. split; [rewrite HX; eapply entails_sound; eauto | exact HGj]. }
  assert (BODY : forall a, etriple segs (I a) (fun w => (exists a', (Zwf 0 a' a) /\ I a' w) \/ Q w)).
  { intros a w (n0 & rho0 & Hin0 & Hsp0 & Hm0 & Ha0).
    apply in_app_or in Hin0 as [Hcut|Hexit].
    - destruct (ROUND n0 rho0 w Hcut Hsp0) as (w' & nj & rhoj & Hsteps & Hinj & Hspj & Hmj).
      exists w'. split; [exact Hsteps|]. left. exists (enj_meas nj rhoj). split; [unfold Zwf; lia|].
      exists nj, rhoj. split; [exact Hinj|]. split; [exact Hspj|]. split; [reflexivity|lia].
    - destruct (Hexits n0 rho0 Hexit w Hsp0) as (w' & Hsteps & [Hfam|Hq]).
      + destruct Hfam as (n1 & rho1 & Hin1 & Hsp1 & Hm1).
        exists w'. split; [exact Hsteps|]. left. exists (enj_meas n1 rho1). split; [unfold Zwf; lia|].
        exists n1, rho1. split; [apply in_or_app; left; exact Hin1|].
        split; [exact Hsp1|]. split; [reflexivity|lia].
      + exists w'. split; [exact Hsteps|]. right. exact Hq. }
  pose proof (@etriple_loop segs Z (Zwf 0) (Zwf_well_founded 0) I Q BODY) as LOOP.
  intros w Hw.
  destruct (Z_lt_le_dec (enj_meas n rho) 0) as [Hneg|Hnn].
  - exfalso. destruct (ROUND n rho w Hin Hw) as (w' & nj & rhoj & _ & _ & _ & Hmj). lia.
  - apply (LOOP (enj_meas n rho)). exists n, rho. split; [apply in_or_app; left; exact Hin|].
    split; [exact Hw|]. split; [reflexivity|lia].
Qed.

Definition to_enodeJ (J : jpred) (n : vnode) : enodeJ := ltac2:(tb__ "0|0|
S21S20S0S3bA2S1S46Frho;S21S0S3bS77Vn;A1VJ;A4S81Vn;A1A4").

Lemma echeck_soundJ : ltac2:(tb__ "0|0|
S45S3bS1bS74A1S73S3eR4R3A2S2dS1cS8fR5R3R2A3S1dA3S6fS47S74S65S6cR5A1R4A4R3A2F_;F_;Fe;Fnodes;FJ;Fg;").
Proof using .
  intros g J nodes e HJ H. unfold echeck in H. unfold eedge_okJ.
  intros Ti Tj Hi Hj rho rho' tr md Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enodeJ enj_state enj_pred enj_meas fst snd] in *.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H Hrk].
  apply andb_prop in H as [H Hvb]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle. apply Z.leb_le in Hrk.
  split.
  - eapply HJ; [|exact Hg]. eapply agree_below_trans.
    + eapply agree_below_le; [exact Hgle | exact Hag].
    + apply rho_sub_agree. exact Hid.
  - unfold vmeas. rewrite <- eval_subst.
    rewrite (eval_agree _ rho rho' (vn_var ni) Hag Hvb).
    pose proof (urange (eval rho' (sv_subst (e_sub e) (vn_var nj)))) as R1.
    pose proof (urange (eval rho' (vn_var ni))) as R2.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + apply Z.ltb_lt in Hlt. nia.
    + apply andb_prop in Heq as [Heq Hu]. apply Z.eqb_eq in Heq.
      pose proof (uleq_sound rho' _ _ 1 _ HF Hu) as U1. unfold U in U1. rewrite Heq. lia.
Qed.

Theorem cfg_complete_autoJ : ltac2:(tb__ "0|2|
S1fS1bS46A1S45S1bS74A1M0G0S3bS36OF_;S3eR5R2A2S2dS1cS8eVsegs;R8R7R6R5R4A6S1dA3S74S1S32S74R2R7A3S38Vsegs;S3dVsegs;R7S77R3A1M1R2A4S36S30S69S47S74S65S6cR8A1RaA4S81R4R3A2R1A3R7R1A1A2Lw;A3F_;Frho;FE;S74S1S32S74R2R9A3S38Vsegs;S3dVsegs;R8G1R2A4R7A3F_;Frho;Fn;F_;F_;F_;FQ;FJ;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits J Q HJ Hchk Hexits n rho Hin.
  unfold check_ecfg in Hchk. apply andb_prop in Hchk as [Hstrict Hchk].
  destruct (cfg_edges segs fuel cutpcs g (map vn_state cuts) (map vn_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (vn_state n) with (enj_state (to_enodeJ J n)). change J with (enj_pred (to_enodeJ J n)) at 1.
  apply (cfg_complete_genJ fuel cutpcs g (map (to_enodeJ J) cuts) (map (to_enodeJ J) exits) es Q).
  - apply forallb_forall. intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0).
    exact (proj1 (forallb_forall _ _) Hstrict m0 Hm0).
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeck_soundJ g J); [exact HJ|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E rhoE HinE. apply in_map_iff in HinE as (E0 & <- & HinE0).
    exact (Hexits E0 rhoE HinE0).
  - apply in_map_iff. exists n. auto.
Qed.

Lemma eexit_postJ : ltac2:(tb__ "0|0|
S3bS45S1S1bS74A1S1bS93A1S74S32S93S96S77R1A1S94A2R2A3S1S38Vsegs;S3dVsegs;S79S1S4R8R7R1A3Lr;R8A2S77R3A1R1A4S36S30S69S47S74S65S6cS79S1S4R9R8R1A3Lr;R9A2A1R6A4S81R4R2A2R1A3S44Vsegs;R9R8R7R5R1A6A2Lw;A3Frho;F_;FP;Fposts;Fcuts;Frho0;Fn;FJ0;").
Proof using .
  intros J0 n rho0 cuts posts P Hin rho w [Hsm [Hag Hk]]. exists w. split; [apply wsteps_refl|].
  right. exists (mkLeaf (vn_state P) RsSymJump), rho. auto.
Qed.

Lemma eexit_reenterJ : ltac2:(tb__ "0|2|
S3bS45S1bS74A1S36OF_;S74S74S1bS2A1S0S9bS32S74R4R7A3S2dS0S77R5A1S76R4R3A2A3S2dS1cSafS77R7A1R4R3A3S1dA3S2dS1cS9dR4RbA2S1dA3S3eRcRdA2S2dS1cS33S2S9S6R7A1A1R8A3S1dA3S1S1bS71A1S72R12R3R2R1A3S48S2S5R4A1S7S77RfA1M0A1A3S48S2S5S9cR5RcA2A1ReA3F_;F_;Fmd;Ftr;Frho;Sa5Sa8S8aRbA1Z1A2S8aRcA1M1A2Sa5Z0G1A2S1S38Vsegs;S3dVsegs;R13G0R1A4S36S30S69S47S74S65S6cR14A1R12A4S81R10R2A2R1A3R11R1A1A2Lw;A3Frho;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fs;FT0;FF;FC;FE;FQ;Fcuts;Fg;FJ;").
Proof using .
  intros J g cuts Q E C F T0 s Hin HC He Hid HJ Hb HF Hrk Hr0 rho w Hsp.
  exists w. split; [apply wsteps_refl|]. left.
  exists (to_enodeJ J C), (rho_sub rho s). split; [apply in_map; exact Hin|].
  cbn [to_enodeJ enj_state enj_pred enj_meas fst snd]. split.
  - rewrite HC. eapply SPJ_entails_sem; eauto.
  - unfold vmeas.
    pose proof (urange (eval (rho_sub rho s) (vn_var C))) as R1.
    pose proof (urange (eval rho (vn_var E))) as R2. nia.
Qed.

Definition nodes_atJ (ok : assn) (nodes : list jnode) (Q : assn) (m : nat) : Prop := ltac2:(tb__ "0|0|
S0S3bS1S32S20S0S3bA2S21S0S3bR3R2A4Vnodes;A3S3aVsegs;Vok;Vm;S3dVsegs;R3R4R2A4VQ;A5F_;Frho;FJ;FT;").

Theorem cfg_sound_recJ : ltac2:(tb__ "0|5|
S1fS1bS46A1S45S1bS66A1M0G0S1bS73A1M1S36OF_;S39S0S3bS32S20S0S3bA2M2S21S0S3bR2R1A4M3R7A3S42Vsegs;R5R2A3F_;FJ;FT;S0S3bS32G2G3R8A3S2dS1cS8R3A1S1dA3S41Vsegs;R7R3A3F_;F_;FJ;FT;S2dS1eG1A1S75Vsegs;RaR9R8S47G2S0S25S0S3bA2M4R7A4S47G2S0G4R6A4A6S22G1R5A2A3S48S73S6dS24S66R8R7A3A1R6A3S1fS0S3bS1S32G2S21S0S3bR3R2A4RcA3S6eRbReRaR5A4S3aVsegs;RcR6S3dVsegs;R4R5R3A4RbA5F_;F_;Frho;FJE;FE;Fm;S1fS6eR8RbR7R1A4Fn;F_;F_;F_;F_;F_;FQ;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok Q Hok Hokf Hes Hedges Hexits n.
  induction n as [|n IH]; intros T J rho HinT.
  - intros _ w _. exact I.
  - destruct (In_nth_error _ _ HinT) as [k Hk].
    assert (HkT : nth_error (map fst cuts) k = Some T) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edges in Hes.
    destruct (cuts_edges_spec segs fuel cutpcs g (map fst cuts) 0 (map fst cuts ++ map fst exits) es Hes k T HkT)
      as (Hle & leaves & Hrun & HL).
    intros HgQS. pose proof (@guards_mono segs ok (S n) n Q ltac:(lia) HgQS) as HgQ.
    apply (sym_run_sound segs fuel cutpcs T leaves ok (J rho) rho Hrun
             ltac:(intros tr ms md ms' Hk'; exact (Hok T J HinT rho tr ms md ms' Hk'))
             ltac:(intros Hlen tr ms md Hk'; exact (Hokf T J HinT Hlen rho tr ms md Hk')) n).
    intros w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent). rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold edge_okJ in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold jnode in *.
    destruct (nth_error (cuts ++ exits) j) as [[Xs JX]|] eqn:HnXG; cbn in HnX; [|discriminate].
    injection HnX as ->.
    destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model liftK] in Hkk.
    assert (HJX : JX (rho_sub rho'' s) tr md).
    { eapply (EOK (T, J) (X, JX)); [| reflexivity | exact Hag | exact Hkk |].
      - rewrite nth_error_app1; [exact Hk|]. apply nth_error_Some. congruence.
      - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
    assert (HSPX : SPJ segs JX X (rho_sub rho'' s) (tr, mkCfg ms md)).
    { split; [eapply entails_sound; eauto | exact HJX]. }
    destruct (Nat.lt_ge_cases j (length cuts)) as [Hj|Hj].
    + rewrite nth_error_app1 in HnXG by exact Hj.
      exact (IH X JX (rho_sub rho'' s) (nth_error_In _ _ HnXG) HgQ _ HSPX).
    + rewrite nth_error_app2 in HnXG by exact Hj.
      exact (Hexits n X JX (rho_sub rho'' s) (nth_error_In _ _ HnXG) IH HgQ _ HSPX).
Qed.

Corollary cfg_sound_recJ_triple : ltac2:(tb__ "0|6|
S1fS1bS46A1S45S1bS66A1M0G0S1bS73A1M1S36OF_;S39S0S3bS32S20S0S3bA2M2S21S0S3bR2R1A4M3R7A3S42Vsegs;R5R2A3F_;FJ;FT;S0S3bS32G2G3R8A3S2dS1cS8R3A1S1dA3S41Vsegs;R7R3A3F_;F_;FJ;FT;S2dS1eG1A1S75Vsegs;RaR9R8S47G2S0S25S0S3bA2M4R7A4S47G2S0G4R6A4A6S22G1R5A2A3S48S73S6dS24S66R8R7A3A1R6A3S1fS0S3bS1S32G2S21S0S3bR3R2A4M5RcA3S6eRbReRaR5A4S3aVsegs;RcR6S3dVsegs;R4R5R3A4RbA5F_;F_;Frho;FJE;FE;Fm;S0S3bS1S32G2G5RdA3S37Vsegs;RbS3dVsegs;R3R4R2A4RaA4F_;Frho;FJ;FT;F_;F_;F_;F_;F_;FQ;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok Q Hok Hokf Hes Hedges Hexits T J rho HinT n.
  exact (cfg_sound_recJ fuel cutpcs g cuts exits es ok Q Hok Hokf Hes Hedges Hexits n T J rho HinT).
Qed.

End CFGJ.
