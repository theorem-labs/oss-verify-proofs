(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Module AX2B.
Import AX2.
Create HintDb bceq discriminated.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma p_aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Scheme kc__1 := Elimination for LinuxProcessSemantics.Riscv.Instr.mulop Sort Prop.
Lemma p_mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mulop_eqb); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.Riscv.Instr.M_MUL); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@LinuxProcessSemantics.Riscv.Instr.M_MULH); constr:(@LinuxProcessSemantics.Riscv.Instr.M_MULHSU); constr:(@LinuxProcessSemantics.Riscv.Instr.M_MULHU); constr:(@LinuxProcessSemantics.Riscv.Instr.M_DIV); constr:(@LinuxProcessSemantics.Riscv.Instr.M_DIVU); constr:(@LinuxProcessSemantics.Riscv.Instr.M_REM); constr:(@LinuxProcessSemantics.Riscv.Instr.M_REMU)|] [|@b; @m; @e; @H0; @a|] "#)8#&#<#)#,#.###3#/#7#8#9#:#;#<#=#$#1#%#&#4#2#5#+#-#6#*#0(#7&#8%#9%#:-#;%$PF#D#E#CRPk##$#k#$C#j#%C#$HF#D#E#CHPk##$#j#%C##DEE'CHj##$#$HH#D#E#CHHk##$#m#'##DQEnD#$#$S#F#%#G#S$j#&D#ZS%DQ#S&EF#CHI%#Fl#'%G#j##)#$HI#D#Ek###(m#&##CHJ%#Fl#'-G#j##1#$HJ#D#Ek###(m#&##CHK%#Fl#'5G#j##9#$HK#D#Ek###(m#&##CHL%#Fl#'=G#j##A#$HL#D#Ek###(m#&##CHM%#Fl#'s#%G#j##s#)#$HM#D#Ek###(m#&##CHN%#Fl#'s#-G#j##s#1#$HN#D#Ek###(m#&##CHO%#Fl#'s#5G#j##s#9#$HO#D#Ek###(m#&#&s#Gs#?s#3s#+s##;3+#Fj#$C#$IF#D#E#CIPk##$#j#%C##CIH%#Fl#'s#DG#j##s#H#$IH#D#Ek###(m#&#'CIj##s#V#$II#D#E#CIIk##$#m#'##CIJ%#Fl#'s#SG#j##s#W#$IJ#D#Ek###(m#&##CIK%#Fl#'s#[G#j##s#_#$IK#D#Ek###(m#&##CIL%#Fl#'s#cG#j##s#g#$IL#D#Ek###(m#&##CIM%#Fl#'s#kG#j##s#o#$IM#D#Ek###(m#&##CIN%#Fl#'s#sG#j##s#w#$IN#D#Ek###(m#&##CIO%#Fl#'s#{G#j##s$##$IO#D#Ek###(m#&#&s#Bs#:s#3s#+s##;3+#Fj#$C#$JF#D#E#CJPk##$#j#%C##CJH%#Fl#'s$.G#j##s$2#$JH#D#Ek###(m#&##CJI%#Fl#'s$6G#j##s$:#$JI#D#Ek###(m#&#'CJj##s$H#$JJ#D#E#CJJk##$#m#'##CJK%#Fl#'s$EG#j##s$I#$JK#D#Ek###(m#&##CJL%#Fl#'s$MG#j##s$Q#$JL#D#Ek###(m#&##CJM%#Fl#'s$UG#j##s$Y#$JM#D#Ek###(m#&##CJN%#Fl#'s$]G#j##s$a#$JN#D#Ek###(m#&##CJO%#Fl#'s$eG#j##s$i#$JO#D#Ek###(m#&#&s#Bs#:s#2s#+s##;3+#Fj#$C#$KF#D#E#CKPk##$#j#%C##CKH%#Fl#'s$tG#j##s$x#$KH#D#Ek###(m#&##CKI%#Fl#'s$|G#j##s%$#$KI#D#Ek###(m#&##CKJ%#Fl#'s%(G#j##s%,#$KJ#D#Ek###(m#&#'CKj##s%:#$KK#D#E#CKKk##$#m#'##CKL%#Fl#'s%7G#j##s%;#$KL#D#Ek###(m#&##CKM%#Fl#'s%?G#j##s%C#$KM#D#Ek###(m#&##CKN%#Fl#'s%GG#j##s%K#$KN#D#Ek###(m#&##CKO%#Fl#'s%OG#j##s%S#$KO#D#Ek###(m#&#&s#Bs#:s#2s#*s##;3+#Fj#$C#$LF#D#E#CLPk##$#j#%C##CLH%#Fl#'s%^G#j##s%b#$LH#D#Ek###(m#&##CLI%#Fl#'s%fG#j##s%j#$LI#D#Ek###(m#&##CLJ%#Fl#'s%nG#j##s%r#$LJ#D#Ek###(m#&##CLK%#Fl#'s%vG#j##s%z#$LK#D#Ek###(m#&#'CLj##s&,#$LL#D#E#CLLk##$#m#'##CLM%#Fl#'s&)G#j##s&-#$LM#D#Ek###(m#&##CLN%#Fl#'s&1G#j##s&5#$LN#D#Ek###(m#&##CLO%#Fl#'s&9G#j##s&=#$LO#D#Ek###(m#&#&s#Bs#:s#2s#*B;3+#Fj#$C#$MF#D#E#CMPk##$#j#%C##CMH%#Fl#'s&HG#j##s&L#$MH#D#Ek###(m#&##CMI%#Fl#'s&PG#j##s&T#$MI#D#Ek###(m#&##CMJ%#Fl#'s&XG#j##s&\#$MJ#D#Ek###(m#&##CMK%#Fl#'s&`G#j##s&d#$MK#D#Ek###(m#&##CML%#Fl#'s&hG#j##s&l#$ML#D#Ek###(m#&#'CMj##s&z#$MM#D#E#CMMk##$#m#'##CMN%#Fl#'s&wG#j##s&{#$MN#D#Ek###(m#&##CMO%#Fl#'s'#G#j##s''#$MO#D#Ek###(m#&#&s#Bs#:s#2s#*B:3+#Fj#$C#$NF#D#E#CNPk##$#j#%C##CNH%#Fl#'s'2G#j##s'6#$NH#D#Ek###(m#&##CNI%#Fl#'s':G#j##s'>#$NI#D#Ek###(m#&##CNJ%#Fl#'s'BG#j##s'F#$NJ#D#Ek###(m#&##CNK%#Fl#'s'JG#j##s'N#$NK#D#Ek###(m#&##CNL%#Fl#'s'RG#j##s'V#$NL#D#Ek###(m#&##CNM%#Fl#'s'ZG#j##s'^#$NM#D#Ek###(m#&#'CNj##s'l#$NN#D#E#CNNk##$#m#'##CNO%#Fl#'s'iG#j##s'm#$NO#D#Ek###(m#&#&s#Bs#:s#2s#*B:2+#Fj#$C#$OF#D#E#COPk##$#j#%C##COH%#Fl#'s'xG#j##s'|#$OH#D#Ek###(m#&##COI%#Fl#'s($G#j##s((#$OI#D#Ek###(m#&##COJ%#Fl#'s(,G#j##s(0#$OJ#D#Ek###(m#&##COK%#Fl#'s(4G#j##s(8#$OK#D#Ek###(m#&##COL%#Fl#'s(<G#j##s(@#$OL#D#Ek###(m#&##COM%#Fl#'s(DG#j##s(H#$OM#D#Ek###(m#&##CON%#Fl#'s(LG#j##s(P#$ON#D#Ek###(m#&#'COj##s(^#$OO#D#E#COOk##$#m#'#&s#Bs#:s#2s#*B:2*#Fj#$C#&s(ls'}s'7s&Ms%cs$ys$3s#I#Fj#(C##"). Qed.
Lemma p_expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply p_aluop_eqb_eq in H
      | H : mulop_eqb _ _ = true |- _ => apply p_mulop_eqb_eq in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint first_var (e : expr) : option nat :=
  match e with
  | ELit _ => None
  | EVar n => Some n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match first_var a with Some n => Some n | None => first_var b end
  | EExt _ _ _ a => first_var a
  | EBlob _ _ _ _ => None
  end.
Definition vkey_of (e : expr) : option nat := first_var (fst (lit_strip e)).   (* [comment removed for export] *)
Fixpoint lset {A : Type} (l : list (list A)) (n : nat) (x : A) {struct n} : list (list A) :=
  match n, l with
  | O, [] => [[x]]
  | O, b :: rest => (x :: b) :: rest
  | S m, [] => [] :: lset [] m x
  | S m, b :: rest => b :: lset rest m x
  end.
Definition lget {A : Type} (l : list (list A)) (n : nat) : list A := nth n l [].
Lemma lget_lset : forall (A : Type) (l : list (list A)) n x m,
  lget (lset l n x) m = if Nat.eqb m n then x :: lget l m else lget l m.
Proof.
  intros A l n. revert l. unfold lget. induction n as [|n IH]; intros l x m; destruct l as [|b rest]; destruct m as [|m]; cbn [lset nth Nat.eqb]; try reflexivity.
  - destruct m; reflexivity.
  - rewrite IH. destruct (Nat.eqb m n); destruct m; reflexivity.
  - apply IH.
Qed.
Record rindex := RI { ri_vars : list (list kentry); ri_other : list kentry }.
Definition ri_bucket (ri : rindex) (k : option nat) : list kentry :=
  match k with Some n => lget (ri_vars ri) n | None => ri_other ri end.
Fixpoint mk_ri (fk : list kentry) : rindex :=
  match fk with
  | [] => RI [] []
  | K :: rest =>
      let t := mk_ri rest in
      match K with
      | KRange e' _ _ =>
          match vkey_of e' with
          | Some n => RI (lset (ri_vars t) n K) (ri_other t)
          | None => RI (ri_vars t) (K :: ri_other t)
          end
      | _ => t
      end
  end.
Definition find_rangeI (ri : rindex) (e : expr) : option (Z * Z) := find_range (ri_bucket ri (vkey_of e)) e.

Definition okey_eqb (a b : option nat) : bool :=
  match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.
Lemma okey_eqb_spec : forall a b, reflect (a = b) (okey_eqb a b).
Proof.
  intros [x|] [y|]; cbn; try (constructor; congruence).
  destruct (Nat.eqb_spec x y); constructor; congruence.
Qed.
Lemma ri_bucket_cons : forall t K e' lo hi k,
  K = KRange e' lo hi ->
  ri_bucket (match vkey_of e' with
             | Some n => RI (lset (ri_vars t) n K) (ri_other t)
             | None => RI (ri_vars t) (K :: ri_other t)
             end) k
  = if okey_eqb k (vkey_of e') then K :: ri_bucket t k else ri_bucket t k.
Proof.
  intros t K e' lo hi k ->. destruct (vkey_of e') as [n|] eqn:Ev; destruct k as [m|]; cbn [ri_bucket ri_vars ri_other okey_eqb]; try reflexivity.
  apply lget_lset.
Qed.
Lemma find_rangeI_eq : forall fk e, find_rangeI (mk_ri fk) e = find_range fk e.
Proof.
  intros fk e. unfold find_rangeI. induction fk as [|K rest IH].
  - cbn [mk_ri]. destruct (vkey_of e) as [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity].
  - cbn [mk_ri]. destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l];
      cbn [find_range]; rewrite <- ?IH; try reflexivity.
    rewrite (ri_bucket_cons (mk_ri rest) _ e' lo hi _ eq_refl).
    destruct (okey_eqb_spec (vkey_of e) (vkey_of e')) as [EQ|NE].
    + cbn [find_range]. rewrite IH. reflexivity.
    + rewrite IH. destruct (expr_eqb e e') eqn:Ee.
      * exfalso. apply NE. apply p_expr_eqb_eq in Ee. subst. reflexivity.
      * destruct (lit_strip e) as [v c] eqn:Lx. destruct (lit_strip e') as [v' c'] eqn:Le'.
        destruct (expr_eqb v v') eqn:Ev.
        -- exfalso. apply NE. unfold vkey_of. rewrite Lx, Le'. cbn [fst]. apply p_expr_eqb_eq in Ev. subst. reflexivity.
        -- destruct e; reflexivity.
Qed.

Record bctx : Type := BC {
  bc_fk : list kentry;      (* [comment removed for export] *)
  bc_ffk : list kentry;     (* [comment removed for export] *)
  bc_fs : list sfact;       (* [comment removed for export] *)
  bc_ri : rindex            (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition mkbc0 (fk : list kentry) (fs : list sfact) : bctx :=
  BC fk (facts_of fk) fs (mk_ri (facts_of fk)).

Lemma lin_range_ext : forall r1 r2 c ts, (forall a, r1 a = r2 a) -> lin_range r1 c ts = lin_range r2 c ts.
Proof. intros r1 r2 c ts H. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite H, IH. reflexivity. Qed.

(* [comment removed for export] *)
Ltac beq_crush rw :=
  repeat (first [ reflexivity
                | progress rw
                | lazymatch goal with
                  | |- ?L = _ =>
                      lazymatch L with
                      | (if ?c then _ else _) => destruct c
                      | (match ?x with _ => _ end) => destruct x
                      end
                  end ]).

Local Open Scope lzb_scope.
Fixpoint erange_fB (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_fB fuel' in
  match find_rangeI (bc_ri bc) e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange bc a with
                 | ELit m, Some (al, ah) =>
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%lzb
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%lzb
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%lzb then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%lzb
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%lzb
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%lzb
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%lzb
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%lzb
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%lzb then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%lzb
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%lzb then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.
Local Close Scope lzb_scope.

Definition erange0B (bc : bctx) (e : expr) : option (Z * Z) := erange_fB erange_fuel bc e.

Definition erangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let r := erange0B bc e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0B bc (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.

Definition base_rangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := (z mod two64)%Z in Some (v, v) | _ => erangeB bc e end.

Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0 (bc_ffk bc) e) (pageup_align e).

Local Open Scope lzb_scope.
Definition lin_nowrapB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%lzb
  | None => false
  end.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Fixpoint srl_expandB (bc : bctx) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expandB bc rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrapB bc e)%lzb then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealignB bc e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrapB bc e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition fact_nowrapB (bc : bctx) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%lzb
  | None => false
  end.
Local Close Scope lzb_scope.

Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expandB bc ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

Fixpoint sum_factsB (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsB bc rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z ++ sum_factsB bc rest
            else sum_factsB bc rest
        | _ => sum_factsB bc rest
        end
      end
  | _ :: rest => sum_factsB bc rest
  end.


(* [comment removed for export] *)
Lemma bc_fk_mkbc0 : forall fk fs, bc_fk (mkbc0 fk fs) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc0 : forall fk fs, bc_ffk (mkbc0 fk fs) = facts_of fk. Proof. reflexivity. Qed.
Lemma find_rangeI_mkbc0 : forall fk fs, find_rangeI (bc_ri (mkbc0 fk fs)) = find_range (facts_of fk).
Proof. intros. apply functional_extensionality. intros e. apply find_rangeI_eq. Qed.
#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).

Lemma erange_fB_eqf0 : forall fk fs fuel, erange_fB fuel (mkbc0 fk fs) = erange_f fuel (facts_of fk).
Proof.
  intros fk fs fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [erange_fB erange_f]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.

Lemma erange0B_eqf0 : forall fk fs, erange0B (mkbc0 fk fs) = erange0 fk.
Proof. intros. bcfe. unfold erange0B, erange0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : forall fk fs, erangeB (mkbc0 fk fs) = erange fk.
Proof. intros. bcfe. unfold erangeB, erange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : forall fk fs, base_rangeB (mkbc0 fk fs) = base_range fk.
Proof. intros. bcfe. unfold base_rangeB, base_range. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Lemma ealignB_eqf0 : forall fk fs, ealignB (mkbc0 fk fs) = ealign fk.
Proof. intros. bcfe. unfold ealignB, ealign. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : forall fk fs, lin_nowrapB (mkbc0 fk fs) = lin_nowrap fk.
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Lemma srl_expandB_eqf0 : forall fk fs, srl_expandB (mkbc0 fk fs) = srl_expand fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sfact); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_expand); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lins_e); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapB); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@Stdlib.Lists.List.fold_right); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.ZArith.BinInt.Z.opp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_rem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.highmask_s); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_nowrap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapB_eqf0); constr:(@kc__2 (@Corelib.Numbers.BinNums.Z) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr))|] [|@ts; @l; @p; @acc; @t; @b; @s; @n; @op0; @a0; @b0; @sx; @lo; @e0; @k0; @i; @x; @mk; @op; @a; @z; @e; @c; @ts'; @IH; @rest; @k; @fs; @fk|] "#%X#5#e#=###>#%#K#(#,#$#&#)#+#-#'#*#<#.#3#/#c#b#2#T#U#f#?#A#D#G#O#R#L#S#W#\#`#0#4#d#e#9#:#E#Q#a#g#h#F#B#;#J#I#@#C#Y#P#M#V#Z#X#]#_#8#N#[#^#H7#T&#U'#V%#<%#W&#X%#;%#Y$#Z%#[%#\%#]%#^(#_$#I%#`$#a%#b&#c&#d)2S:2S;VQCE2#VQC#%JDUS+#US,J%KF)#D&KD')$#j#$+#US<-&F#VS--#%HO)#D&HD'1$#%LHWS.5FJ)$#&L$'6$#k##(#k#%9#j#&;#%MP)#D&MD'=$#&IJ#PLJ$CAF##IMK$Cs##O#*S=US/#+DS0*%*#*#*#*#US/#+)#3+#+N#VS1#S2%S#S'VS(#FnG#$##G%#%###S)VS3%F,*#-N*US4F4Cs#8#(%#.H#+FS0+#23:#-S$#4CEJ($#5CEJ#$#Dj#'s#C#j#(s#E#5Cs#E0/s#Fs#G$O#$Cs#G/#04VS5F=#$#&$Cs#K3#nG#$##s#K9#%#'###NIO$Cs#NH#nG#$##s#N>#%#%###S$RL$Cs#QP##S6S$P$Cs#SM#nE#$#)s#SD#+$#*'$#+(&#,#-#.%&#,#-#.%&#,#-#.%&#,#-#.%'#/#0#+#1#'#/#2#3#+#US>D%S7S#VS(#KUS4K4Cs#Y#(R#.L#0R3s#:DVS5K#(S6B##ADj#'s#a#j#(s#c#5Cs#c-/s#ds#e$H##+)#$Cs#f-##RNH$Cs#hL#nG#$##s#h4#%#%##nS&$C$#4s#i7#%$#*##>nE#$#)s#jD#+$#5#$#+?&#,#-#.<&#,#-#.<&#,#-#.<&#,#-#.<'#/#0#+#1:'#/#2#3#+:nS%#$#6s#kF#-#s#K#s#K#s#K#s#K#s#K#s#K#:#s#K#s#K##nE#$#7s#lH#+$#8s#N$#+s#N&#6#9#)#&#6#-#)s#L&#6#-#)s#L&#6#-#)s#L'#/#0#+#9A'#/#2#3#+AnQ%Cs#n$#4s#mD#$%#:#;#&NF1S#FVS8s#C#VS*S#F,s#H#nG#$##s#s##%#s#/#s#+nG#$##s#t&#%###s#)nE#$#)s#uD#+$#*#$#+s#*&#,#-#.s#'&#,#-#.s#'&#,#-#.s#'&#,#-#.s#''#/#0#+#1s#%'#/#2#3#+s#%1S7KnG#$##s#w##%#4#2nS&$C$#4s#xs#&#%$#*##s#-nE#$#)s#yD#+$#5#$#+s#.&#,#-#.s#+&#,#-#.s#+&#,#-#.s#+&#,#-#.s#+'#/#0#+#1s#)'#/#2#3#+s#)nS%#$#6s#zF#-#s#Z#s#Z#s#Z#s#Z#s#Z#s#Z#'#s#Z#s#Z##nE#$#7s#{H#+$#8s#]$#+s#]&#6#9#)#&#6#-#)s#[&#6#-#)s#[&#6#-#)s#['#/#0#+#9s#0'#/#2#3#+s#0nQ%Cs#}$#4s#|0#$%#:#;#'s#}2#j#&s#~#k#9EGUS9IULFnG#$##Gs#U#%###S)nG#$##s$'##%#s#:#s#8nE#$#)s$(D#+$#*#$#+s#9&#,#-#.s#6&#,#-#.s#6&#,#-#.s#6&#,#-#.s#6'#/#0#+#1s#4'#/#2#3#+s#4UPKnG#$##s$*##%#s###AnS&$C$#4s$+s#5#%$#*##s#<nE#$#)s$,D#+$#5#$#+s#=&#,#-#.s#:&#,#-#.s#:&#,#-#.s#:&#,#-#.s#:'#/#0#+#1s#8'#/#2#3#+s#8nS%#$#6s$-F#-#s#i#s#i#s#i#s#i#s#i#s#i#'#s#i#s#i##nE#$#7s$.H#+$#8s#l$#+s#l&#6#9#)#&#6#-#)s#j&#6#-#)s#j&#6#-#)s#j'#/#0#+#9s#?'#/#2#3#+s#?nQ%Cs$0$#4s$/?#$%#:#;#'s$0#2j#)0#k#9ECUS*InG#$##Gs#c#%#s###S),s#g2nG#$##s$6##%#s#N#s#JnG#$##s$7%#%###s#HnE#$#)s$8D#+$#*#$#+s#I&#,#-#.s#F&#,#-#.s#F&#,#-#.s#F&#,#-#.s#F'#/#0#+#1s#D'#/#2#3#+s#DnS%#$#6s$9F#-#s#u#s#u#s#u#s#u#s#u#s#u###s#u#s#u#>nE#$#7s$:H#+$#8s#x$#+s#x&#6#9#)#&#6#-#)s#v&#6#-#)s#v&#6#-#)s#v'#/#0#+#9s#K'#/#2#3#+s#KnQ%Cs$<$#4s$;s#+#$%#:#;#'s$<#>j#8-##LHJ$Cs$@F##MPK$Cs$BO#+Is#sVS1#S21S'FVS8$#VS*S'F,s#y#-Is#y(#s#p.H#-Rs#m(#s#l##s#kDj#'s$O#j#(s$Q#/s$Qs$R#Os#j$Cs$R)#0,##s#i%$Cs$U,#nG#$##s$U0#%#&###IMO$Cs$XH#nG#$##s$X5#%#%###RNL$Cs$[P##S$RP$Cs$]M#nE#$#)s$]D#+$#*'$#+(&#,#-#.%&#,#-#.%&#,#-#.%&#,#-#.%'#/#0#+#1#'#/#2#3#+#1S#K(Ns#e.L#0N(S$s$&##s$%Dj#'s$e#j#(s$g#/s$gs$h#Hs#b#(s#h#$Cs$i*##NIH$Cs$kL#nG#$##s$k/#%#%##nS&$C$#4s$ls#v#%$#*##7nE#$#)s$mD#+$#5#$#+8&#,#-#.5&#,#-#.5&#,#-#.5&#,#-#.5'#/#0#+#13'#/#2#3#+3nS%#$#6s$nF#-#s#/#s#/#s#/#s#/#s#/#s#/#3#s#/#s#/##nE#$#7s$oO#+$#8s#2$#+s#2&#6#9#)#&#6#-#)s#0&#6#-#)s#0&#6#-#)s#0'#/#0#+#9:'#/#2#3#+:nQ%Cs$q$#4s$ps$T#$%#:#;#VS-s$q#%IMUS3#VS?IM6s#Es#Ds#:&$#US(&VS@IM6s#Ws#Vs#I%$#))J6s$zs$^s#Z$#D$CEKFWS.s$~#J)-#&I$'s%#$#m#(#j#<s$f#j#=s%'#j#7E#j#>C#V#JDj#9E#j#8C#YSACEs$q#Dj#-s%/#YSBs%0s%&s%##Dj#$s%0#YSCs%1s%0s%.s%-#j#?s%4#j#@s%6##"). Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : forall fk fs, fact_nowrapB (mkbc0 fk fs) = fact_nowrap fk.
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : forall fk fs, sum_fact_xB (mkbc0 fk fs) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_eqf0 : forall fk fs, sum_factsB (mkbc0 fk fs) = sum_facts fk.
Proof.
  intros fk fs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_factsB sum_facts]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.


(* [comment removed for export] *)
Definition mkbc (fk : list kentry) : bctx := mkbc0 fk (sum_factsB (mkbc0 fk []) fk).
Lemma bc_fk_mkbc : forall fk, bc_fk (mkbc fk) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : forall fk, bc_ffk (mkbc fk) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_fs_mkbc : forall fk, bc_fs (mkbc fk) = sum_facts fk fk.
Proof. intros. unfold mkbc. cbn [bc_fs mkbc0]. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma find_rangeI_mkbc : forall fk, find_rangeI (bc_ri (mkbc fk)) = find_range (facts_of fk).
Proof. intros. unfold mkbc. apply find_rangeI_mkbc0. Qed.
#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc find_rangeI_mkbc : bceq.
Lemma erange_fB_eqf : forall fk fuel, erange_fB fuel (mkbc fk) = erange_f fuel (facts_of fk).
Proof. intros. unfold mkbc. apply erange_fB_eqf0. Qed.
#[export] Hint Rewrite erange_fB_eqf : bceq.

Lemma erange0B_eqf : forall fk, erange0B (mkbc fk) = erange0 fk.
Proof. intros. unfold mkbc. apply erange0B_eqf0. Qed.
#[export] Hint Rewrite erange0B_eqf : bceq.
Lemma erangeB_eqf : forall fk, erangeB (mkbc fk) = erange fk.
Proof. intros. unfold mkbc. apply erangeB_eqf0. Qed.
#[export] Hint Rewrite erangeB_eqf : bceq.
Lemma base_rangeB_eqf : forall fk, base_rangeB (mkbc fk) = base_range fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sum_factsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc0); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sfact); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range)|] [|@e; @fk|] "##1#$#3###2#'#(#,#-#+#*#)#1#0#/#4#3#5#.#UEFUGHVIC#VJ#CVKC#VLDDUM#k#$N#UOCUP#UQCWR&$#m#*#j#%/##"). Qed.
#[export] Hint Rewrite base_rangeB_eqf : bceq.
Lemma ealignB_eqf : forall fk, ealignB (mkbc fk) = ealign fk.
Proof. intros. unfold mkbc. apply ealignB_eqf0. Qed.
#[export] Hint Rewrite ealignB_eqf : bceq.
Lemma lin_nowrapB_eqf : forall fk, lin_nowrapB (mkbc fk) = lin_nowrap fk.
Proof. intros. unfold mkbc. apply lin_nowrapB_eqf0. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Lemma srl_expandB_eqf : forall fk, srl_expandB (mkbc fk) = srl_expand fk.
Proof. intros. unfold mkbc. apply srl_expandB_eqf0. Qed.
#[export] Hint Rewrite srl_expandB_eqf : bceq.
Lemma fact_nowrapB_eqf : forall fk, fact_nowrapB (mkbc fk) = fact_nowrap fk.
Proof. intros. unfold mkbc. apply fact_nowrapB_eqf0. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Lemma sum_fact_xB_eqf : forall fk, sum_fact_xB (mkbc fk) = sum_fact_x fk.
Proof. intros. unfold mkbc. apply sum_fact_xB_eqf0. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Lemma sum_factsB_eqf : forall fk, sum_factsB (mkbc fk) = sum_facts fk.
Proof. intros. unfold mkbc. apply sum_factsB_eqf0. Qed.
#[export] Hint Rewrite sum_factsB_eqf : bceq.

Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match bc_fs bc with
  | [] => false
  | fs =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeB bc) c ts' with
          | Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
          | None => false
          end
      | _ => false
      end
  end.

Definition lin_testB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
  | None => lin_test_relB bc c ts test
  end.

Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expandB bc ts in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    match lin_range (erangeB bc) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

Local Open Scope lzb_scope.
Definition lin_nowrapRB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expandB bc (snd l) in            (* [comment removed for export] *)
  if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%lzb) then true
  else (* [comment removed for export] *)
    match lin_srangeB bc e with Some _ => true | None => false end.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%lzb))%lzb.
Local Close Scope lzb_scope.

Definition lin_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0B bc b1 k1 n1 b2 k2 n2 else false.

Local Open Scope lzb_scope.
Definition lin_brangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match bc_fs bc with
  | [] => None
  | fs =>
      match sum_subst fs (snd l) 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeB bc) (fst l) ts' with
          | Some (lo, hi) =>
              let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
              if (Z.leb 0 lo' && Z.ltb hi' two64)%lzb then Some (lo', hi') else None
          | None => None
          end
      | _ => None
      end
  end.
Local Close Scope lzb_scope.

Definition xloB (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e with
         | Some (lo, _) => Some lo
         | None => match lin_brangeB bc e with
                   | Some (lo, _) => Some lo
                   | None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

Definition xhiB (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e with
         | Some (_, hi) => Some hi
         | None => match lin_brangeB bc e with
                   | Some (_, hi) => Some hi
                   | None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

Local Open Scope lzb_scope.
Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r end.
Local Close Scope lzb_scope.

Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expandB bc ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

Definition lin_galignB (bc : bctx) (c : Z) (ts : list (Z * expr)) : Z :=
  fold_right (fun t g => Z.min g (ctz64 (fst t) + ealignB bc (snd t)))%Z (ctz64 c) ts.
Definition lin_ge0_alB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let g := Z.min (lin_galignB bc c ts) 16 in
  if Z.ltb 0 g then
    let thr := (1 - 2 ^ g)%Z in
    if lin_testB bc c ts (fun lo _ => Z.leb thr lo) then true
    else let '(c2, t2) := srl_expandB bc ts in lin_testB bc (c + c2)%Z t2 (fun lo _ => Z.leb thr lo)
  else false.

Local Open Scope lzb_scope.
Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  (xt_nowrapB bc pos && xt_nowrapB bc neg &&
   (* [comment removed for export] *)
   (if lin_testB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_testB bc (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expandB bc t2 in
               lin_testB bc (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else (* [comment removed for export] *)
         if lin_ge0_scaledB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) then true
         else (* [comment removed for export] *)
           lin_ge0_alB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))))%lzb.
Local Close Scope lzb_scope.

Definition xinside0B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0B bc [(b1, k1)] [(b2, k2)] then lin_ge0B bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.

Local Open Scope lzb_scope.
Definition xinside_numB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Local Close Scope lzb_scope.

Definition xinsideB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then
    (if xinside_numB bc b1 k1 n1 b2 k2 n2 then true
     else if novars n1 then false else xinside0B bc b1 k1 n1 b2 k2 n2)   (* [comment removed for export] *)
  else false.

Local Open Scope lzb_scope.
Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%lzb then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else (* [comment removed for export] *)
    if (Z.leb 0 n && Z.ltb n two64)%lzb then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false.
Local Close Scope lzb_scope.

Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  end.

Local Open Scope lzb_scope.
Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_rangeB bc b1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%lzb
      | _, _ => false
      end) then true
  else if kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Local Close Scope lzb_scope.

Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  xinsideB bc b k n (a_base c) (a_off c) m.

Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  end.

Definition end_hiB (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match find_rangeI (bc_ri bc) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
              | Some (_, ehi) => Some ehi
              | None => None
              end
         else None
  end.

Local Open Scope lzb_scope.
Definition ranges_apart_xB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%lzb then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Local Close Scope lzb_scope.

Fixpoint disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesB bc rest b1 k1 n1 in
      let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesB bc rest b1 k1 n1
  end.

(* [comment removed for export] *)
Definition sdmemo : Type := list (saddr * expr * bool).
Local Open Scope lzb_scope.
Fixpoint sdm_find (c : saddr) (m : expr) (mm : sdmemo) : option bool :=
  match mm with
  | [] => None
  | (c', m', r) :: rest => if (saddr_eqb c c' && expr_eqb m m')%lzb then Some r else sdm_find c m rest
  end.
Local Close Scope lzb_scope.
Definition sub_itvM (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) (mm : sdmemo) : bool * sdmemo :=
  if expr_eqb b (a_base c) then (sub_itvB bc b k n c m, mm)
  else if (if shares_var b (a_base c) then true else novars (a_base c)) then    (* [comment removed for export] *)
    match sdm_find c m mm with
    | Some r => (r, mm)
    | None => let r := sub_itvB bc b k n c m in (r, (c, m, r) :: mm)
    end
  else (sub_itvB bc b k n c m, mm).
Fixpoint disj_sidesM (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (mm : sdmemo) : list (saddr * expr) * sdmemo :=
  match kn with
  | [] => ([], mm)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(t2, mm1) := sub_itvM bc b1 k1 n1 c2 m2 mm in
      let '(t1, mm2) := sub_itvM bc b1 k1 n1 c1 m1 mm1 in
      let '(r, mm3) := disj_sidesM bc rest b1 k1 n1 mm2 in
      let r1 := if t2 then (c1, m1) :: r else r in
      (if t1 then (c2, m2) :: r1 else r1, mm3)
  | _ :: rest => disj_sidesM bc rest b1 k1 n1 mm
  end.
Definition sdm_ok (bc : bctx) (b1 : expr) (k1 n1 : Z) (mm : sdmemo) : Prop :=
  forall c m r, In (c, m, r) mm -> r = sub_itvB bc b1 k1 n1 c m.
Lemma sdm_find_ok : forall bc b1 k1 n1 mm c m r, sdm_ok bc b1 k1 n1 mm -> sdm_find c m mm = Some r -> r = sub_itvB bc b1 k1 n1 c m.
Proof.
  intros bc b1 k1 n1 mm c m r Hok. induction mm as [|[[c' m'] r'] rest IH]; cbn [sdm_find]; [discriminate|].
  change (if saddr_eqb c c' then expr_eqb m m' else false) with (saddr_eqb c c' && expr_eqb m m')%bool in *; destruct (saddr_eqb c c' && expr_eqb m m')%bool eqn:He.
  - intros H. injection H as <-. apply andb_prop in He as [Hc Hm]. apply p_expr_eqb_eq in Hm. subst m'.
    unfold saddr_eqb in Hc. apply andb_prop in Hc as [Hb Ho]. apply p_expr_eqb_eq in Hb. apply Z.eqb_eq in Ho.
    destruct c as [cb co], c' as [cb' co']. cbn [a_base a_off] in Hb, Ho. subst cb' co'. apply Hok. left; reflexivity.
  - apply IH. intros c0 m0 r0 Hin. apply Hok. right; exact Hin.
Qed.
Lemma sub_itvM_ok : forall bc b1 k1 n1 c m mm, sdm_ok bc b1 k1 n1 mm ->
  fst (sub_itvM bc b1 k1 n1 c m mm) = sub_itvB bc b1 k1 n1 c m /\ sdm_ok bc b1 k1 n1 (snd (sub_itvM bc b1 k1 n1 c m mm)).
Proof.
  intros bc b1 k1 n1 c m mm Hok. unfold sub_itvM.
  destruct (expr_eqb b1 (a_base c)); [split; [reflexivity | exact Hok]|].
  destruct (if shares_var b1 (a_base c) then true else novars (a_base c)); [|split; [reflexivity | exact Hok]].
  destruct (sdm_find c m mm) as [r|] eqn:Hf; cbn [fst snd].
  - split; [exact (sdm_find_ok _ _ _ _ _ _ _ _ Hok Hf) | exact Hok].
  - split; [reflexivity|]. intros c0 m0 r0 [H|H]; [injection H as <- <- <-; reflexivity | exact (Hok _ _ _ H)].
Qed.
Lemma disj_sidesM_ok : forall bc kn b1 k1 n1 mm, sdm_ok bc b1 k1 n1 mm ->
  fst (disj_sidesM bc kn b1 k1 n1 mm) = disj_sidesB bc kn b1 k1 n1 /\ sdm_ok bc b1 k1 n1 (snd (disj_sidesM bc kn b1 k1 n1 mm)).
Proof.
  intros bc kn b1 k1 n1. induction kn as [|K rest IH]; intros mm Hok; [split; [reflexivity | exact Hok]|].
  destruct K; cbn [disj_sidesM disj_sidesB]; try (apply IH; exact Hok).
  lazymatch goal with |- context [sub_itvM bc b1 k1 n1 ?c2 ?m2 mm] =>
    destruct (sub_itvM_ok bc b1 k1 n1 c2 m2 mm Hok) as [E2 O2]; destruct (sub_itvM bc b1 k1 n1 c2 m2 mm) as [t2 mm1] end.
  cbn [fst snd] in E2, O2.
  lazymatch goal with |- context [sub_itvM bc b1 k1 n1 ?c1 ?m1 mm1] =>
    destruct (sub_itvM_ok bc b1 k1 n1 c1 m1 mm1 O2) as [E1 O1]; destruct (sub_itvM bc b1 k1 n1 c1 m1 mm1) as [t1 mm2] end.
  cbn [fst snd] in E1, O1.
  destruct (IH mm2 O1) as [ER OR]. destruct (disj_sidesM bc rest b1 k1 n1 mm2) as [r mm3]. cbn [fst snd] in ER, OR |- *.
  subst t1 t2 r. split; [reflexivity | exact OR].
Qed.
Lemma disj_sidesM_eq : forall bc kn b1 k1 n1, fst (disj_sidesM bc kn b1 k1 n1 []) = disj_sidesB bc kn b1 k1 n1.
Proof. intros. apply disj_sidesM_ok. intros c m r []. Qed.

Fixpoint disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_xB bc rest b1 k1 n1 in
      let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_xB bc rest b1 k1 n1
  end.

Fixpoint in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2
  end.

Fixpoint in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2
  end.

Definition mk_sprepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  SPrep (base_rangeB bc b1) (xhiB bc n1)
        (match n1 with ELit z1 => fst (disj_sidesM bc (bc_fk bc) b1 k1 (zlit64 z1) []) | _ => [] end)   (* [comment removed for export] *)
        (fun _ => disj_sides_xB bc (bc_fk bc) b1 k1 n1).

Local Open Scope lzb_scope.
Definition ranges_apart_pB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_rangeB bc b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%lzb
          | _, _ => false
          end) then true
      else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%lzb then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp tt) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Local Close Scope lzb_scope.

Lemma lin_test_relB_eqf : forall fk, lin_test_relB (mkbc fk) = lin_test_rel fk.
Proof. intros. bcfe. unfold lin_test_relB, lin_test_rel. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Lemma lin_testB_eqf : forall fk, lin_testB (mkbc fk) = lin_test fk.
Proof. intros. bcfe. unfold lin_testB, lin_test. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_testB_eqf : bceq.
Lemma lin_srangeB_eqf : forall fk, lin_srangeB (mkbc fk) = lin_srange fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_srange); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_expand); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_scale_need); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.has_srl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zcdiv); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB_eqf)|] [|@ts; @t; @p; @lo'; @hi'; @x; @c3; @t3; @c2; @t2; @e; @o; @fk|] "#$[#,#X#5###<#$#4#2#F#3#>#%#&#'#/#6#8#:#E#B#G#)#N#(#P#Q#R#S#T#9#0#D#L#+#U#*#W#X#Y#Z#1#@#=#A#?#J#H#C#I#O#M#7#K#V#;3#J&#K%#L$#M$#N%#O'#P$#Q%#R%#S&#2%#'%#T$#U&#V$#W&UOS/.CCUJ#/DUP#UQD.CHUO#.C#k#$$#URF%F#C'#&#$K#US0S#)#)#)#US$#$)#nE#$##E)#%###I)S#US$#%L#C4#&#'&#0CHD*$##CHD(CH$#j#%<#XS%==#7UD#US1DULD(C@KDnE#$##@%#%#$##/S&US'#%S(#Cs#%#&#'7#0Cs#(&*$#+#M+#F,+#D%S2#Cs#.#&#'@#VS)F#$K#VS*D%$%#VS+$S,nE#$##E$#%###InE#$##E'#%###I(CC)'VS-s#?#US3s#@nE#$##s#@&#%#$##nG%CC$#&s#AD#$%#'#(#nJ$s#C$#)s#B3#%$#&##%nG%Cs#>$#)s#C?#$%#*#+#nG%Cs#?$#)s#Ds#$#$%#,#-#nE#$##s#Es#2#%###(-Ls#'-NDnE#$##s#Bs#'#%###s#%1S&,#<DnJ$s#L$#)s#K##%$#&,#.nG%Cs#G$#)s#L&#$%#*#+#nG%Cs#H$#)s#M)#$%#,#-#nE#$##s#Ns#;#%###12s#O,#j#&s#I#k#.Hs#Q1F,Ns#%DnJ$s#U$#)s#T##%$#&5#7nG%Cs#P$#)s#U/#$%#*#+#nG%Cs#Q$#)s#V2#$%#,#-#nE#$##s#Ws#D#%###:2s#X#,j#/*#%D#Cs#V#&#$K#$$s#MnE#$##E$#%###I's#Ks#U*#s#G(CH#s#Fj#%s#_#XS%s#`s#`#+-F#-MDnE#$##s#as#F#%###s#D1S(%N#Cs#e#&#'s#W#0Cs#h&*$#+#M+#F,+#D%S4#Cs#n#&#'s#`#VS)F#$K#VS*D%$%#VS+$S,nE#$##E$#%###InE#$##E'#%###I(CC)'VS-s$##nE#$##s$#%#%###s#BnG%CC$#&s$$D#$%#'#(#nJ$s$&$#)s$%2#%$#&##s#DnG%Cs#}$#)s$&=#$%#*#+#nG%Cs#~$#)s$'@#$%#,#-#nE#$##s$(s#'#%###s#GVS5s$)#/FUS'#US6FZS.s#:s#9s#2&$#US7&US8FZS.s$)s$(s#>%$#VP)DVQFD2s$3$#m#&#j#)H#YS9Hs$6s$4s$3#j#0s$9##"). Qed.
#[export] Hint Rewrite lin_srangeB_eqf : bceq.
Lemma lin_nowrapRB_eqf : forall fk, lin_nowrapRB (mkbc fk) = lin_nowrapR fk.
Proof. intros. bcfe. unfold lin_nowrapRB, lin_nowrapR. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapRB_eqf : bceq.
Lemma lin_apart0B_eqf : forall fk, lin_apart0B (mkbc fk) = lin_apart0 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apart0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_apart0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_nowrapR); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lsub_e); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.ZArith.BinInt.Z.opp); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_test); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapRB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapRB_eqf)|] [|@n2; @k2; @b2; @n1; @k1; @e; @hi; @lo; @b; @test; @ts; @c; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "#$<#+#J#2#3###$#%#)#&#(#1#4#6#'#:#*#G#.#8#=#A#E#;#H#7#/#?#D#I#J#K#L#5#0#@#>#<#B#C#F#9-#A$#B(#C$#D&#E%#F&#G%#3%#H%#I&URS*k#$CDk#%C#k#&K#k#'C#k#(C##EUL#UME#FVL#EVMFE#GWL#FEWMGFE#IXL#GFEXMIGFE#NYL#IGFEYMNIGFE#JZL#NIGFEZMJNIGFEk#)KDUS#HUEHUEInD#$##D$#%###O#PVS+CKUR#%I&C$#VS$#G%H&C'#'%#'#J(C*)(C+'VS%$#)HFUS&I)E#nD#$##D%#%#S,##j#*C#j#+C#XS'5,)#nD#$##D7#%###O*PH*PI+$#VS(-+j#*C#j#+C#XQP41#+'#,D+#j#,s#%#k##CDk##C#k#-#Dk#.B#k#/C#UQHnD#$##D2#%#1#OWE?<6nD#$##D$#%###O,D#.j#,(#*HJ*HG+$#%G&Cs#.#VS$#F%J&Cs#1#'%#'#N(Cs#4)(Cs#5'VS%$#)JFUS&G)E#VS(%#j#*C#j#+C#XQH,)#+4#VS-D##HUS'#US.HZS)BA<&$#US/&US0HZS)s#Ms#Ls#*%$#[L)JNIGFE[MHJNIGFE,D$#m#&#j#0C#$CDs#Us#T#j#1C#$Cs#ls#Zs#Y#j#2K#$Ks#ms#_s#^#j#3C#$Cs#ns#ds#c#j#4C#$Cs#os#is#h#j#5K#$Ks#ps#ns#m#j#6s#v##"). Qed.
#[export] Hint Rewrite lin_apart0B_eqf : bceq.
Lemma lin_apartB_eqf : forall fk, lin_apartB (mkbc fk) = lin_apart fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apartB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_apart); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_apart0); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.shares_var); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apart0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apart0B_eqf)|] [|@n2; @k2; @b2; @n1; @k1; @b1; @b; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##]#+#<###$#%#2#&#3#'#(#)#4#6#1#8#;#:#9#.#/#*#<#=#>#7#5#0%#:$#;(US#S$k#$FHk#%F#k#&N#k#'F#k#(F##CUL#UMC#DVL#CVMDC#EWL#DCWMEDC#GXL#EDCXMGEDC#IYL#GEDCYMIGEDC#JZL#IGEDCZMJIGEDCk#)N5UOKVQKGZCKJIGEDnH#$##H$#%###P[OS%KJIGEDnH#$##H&#%###PWRH%#j#**#VQJE[OKJIGEDCnH#$##H$#%###PVS&H##KUS'#US(KZS)21*&$#[L&JIGEDC[MKJIGEDCWRH$#m#&#j#+F#$FH:9#j#,F#$Fs#1?>#j#-N#$Ns#2s#$s###j#.F#$Fs#3s#)s#(#j#/F#$Fs#4s#.s#-#j#0N#$Ns#5s#3s#2#j#1s#;##"). Qed.
#[export] Hint Rewrite lin_apartB_eqf : bceq.
Lemma lin_brangeB_eqf : forall fk, lin_brangeB (mkbc fk) = lin_brange fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_brange); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sfact); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fs); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sum_subst); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_range); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sum_facts); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fs_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf)|] [|@e; @p; @lo; @hi; @x; @b; @p0; @lo0; @hi0; @ts'; @s; @l0; @o; @l; @fk|] "##{#.#P#7#6###$#A#>#5#&#F#'#1#4#%#G#8#:#?#D#B#,#I#+#K#P#;#2#@#C#J#L#M#O#N#-#Q#R#S#T#U#3#E#9#<#H#=*#K$#-$#$%#L$#M$#N&#O&$S,%CCUI#&EUQ#UREk#$N&'F&OUS##US-+%CN$#%#.WS.HFE#JWS$C&#YS%%#KKP#S&WS'C)#(S(#JVS)FLVS/K#VS)EJVS0#S1nG#$##G%#%###PXS2CC'%VS3<#nG#$##<%#%###4nD%CC$#%=E#$%#&#'#nI$?$#(>,#%$#%##6nG#$#)?L#%###7nD%CC$#*@E#$%#+#,#nD%7B$#%AF#$%#-#*#nD%7G$#(B3#$%#%#)#nM$H$#(s##<#%#;%#.#/#VS*OO'S4(#5JVS531nG#$##s#(##%#/#@nD%CC$#%s#)E#$%#&#'#nI$s#+$#(s#*&#%$#%##BnG#$#)s#+L#%###s##nD%CC$#*s#,E#$%#+#,#nD%s##s#.$#%s#-F#$%#-#*#nD%s##G$#(s#.?#$%#%#)#nM$H$#(s#/-#%#s#'%#.#/#)s#0/#j#0s#-#$HVS*FFnI$s#5$#(s#40#%$#%9#s#,nG#$#)s#5L#%###s#-nD%CC$#*s#6E#$%#+#,#nD%s#-s#8$#%s#7F#$%#-#*#nD%s#-G$#(s#8s#)#$%#%#)#nM$H$#(s#9E#%#s#1%#.#/#)s#:#-j#1+##OWS$Cs#3#YS%s#2#KKP'S&#S(WS'Cs#7#(%#JnI$s#D$#(s#C##%$#%<#s#;nG#$#)s#DL#%###s#<nD%CC$#*s#EE#$%#+#,#nD%s#<s#G$#%s#FF#$%#-#*#nD%s#<G$#(s#G+#$%#%#)#nM$H$#(s#H7#%#s#@%#.#/#VS6s#I#&FUS##US7FZS+=<4&$#US8&US9FZS+s#Ls#KA%$#VQ)EVRFE)s#S$#m#&#j#(N#YS:Ns#Vs#Ts#S#j#2s#Y##"). Qed.
#[export] Hint Rewrite lin_brangeB_eqf : bceq.
Lemma xloB_eqf : forall fk, xloB (mkbc fk) = xlo fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xlo); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_brange); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_srange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB_eqf)|] [|@e; @p; @lo; @z; @x; @n; @op; @a; @b; @sx; @e0; @k; @i; @o; @fk|] "#$3#*#C#1#$#(#'#%#2#0#&###)#3#5#7#8#:#@#?#<#=#-#.#;#>#A#B#C#D#E#/#4#9#6+#@$#3%#0%#2%#A&#4%#5%#B)US&S'UCH#KUM#UNKVOHHUC#k#$I#UPDUS(KVQH##J(#GVQHDnO%HH$#%/K#$%#&#'#UDG)'GUS)HnC$/$#(3$#%$#%&##nC$0$#(4&#%$#%'##nC$1$#(5*#%$#%(###E(#FUJF)%FnC$6$#(:##%$#%-#*nC$7$#(;%#%$#%.##nC$8$#(<'#%$#%/###L(#EUFE)%EnC$=$#(A##%$#%4#1nC$>$#(B%#%$#%5##nC$?$#(s##'#%$#%6##nI#$#$s#$D#+$#';$#)1&#*#+#,*&#*#+#,*&#*#+#,*&#*#+#,*'#-#&#)#.#'#-#/#0#)#$JG%JG&JGnC$s#$$#(s#(##%$#%;#8nC$s#%$#(s#)%#%$#%<##nC$s#&$#(s#*'#%$#%=##$EF%EF&EFnC$s#*$#(s#.##%$#%A#>nC$s#+$#(s#/%#%$#%B##nC$s#,$#(s#0'#%$#%s####$LE%LE&LEnC$s#0$#(s#4##%$#%s#'#s#$nC$s#1$#(s#5%#%$#%s#(##nC$s#2$#(s#6'#%$#%s#)##nI#$#$s#7D#+$#'s#.$#)/&#*#+#,)&#*#+#,)&#*#+#,)&#*#+#,)'#-#&#)#.#'#-#/#0#)#'s#86#j#1s#3#URDnC$s#7$#(s#;s#-#%$#%s#.#s#+nC$s#8$#(s#<8#%$#%s#/##nC$s#9$#(s#=s#2#%$#%s#0##nC$s#:$#(s#>s#(#%$#%s#1#s#.nC$s#;$#(s#?5#%$#%s#2##nC$s#<$#(s#@s#+#%$#%s#3##nC$s#=$#(s#As#$#%$#%s#4#s#1nC$s#>$#(s#B2#%$#%s#5##nC$s#?$#(s#Cs#'#%$#%s#6##nI#$#$s#DD#+$#'s#;$#))&#*#+#,&&#*#+#,&&#*#+#,&&#*#+#,&'#-#&#)#.#'#-#/#0#)#'s#E#0j#1s#@#US#DnC$s#D$#(s#Hs#:#%$#%s#;#AnC$s#E$#(s#Is#3#%$#%s#<#<nC$s#F$#(s#Js#-#%$#%s#=#7nI#$#$s#KD#+$#'s#B$#)%&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#&#)#.#'#-#/#0#)#'s#L#7j#1s#G#$GD%GD&GDnC$s#M$#(s#Q##%$#%s#D#s#AnC$s#N$#(s#R%#%$#%s#E##nC$s#O$#(s#S'#%$#%s#F##$FJ%FJ&FJnC$s#S$#(s#W##%$#%s#J#s#GnC$s#T$#(s#X%#%$#%s#K##nC$s#U$#(s#Y'#%$#%s#L##nI#$#$s#ZK#+$#'s#Q$#))&#*#+#,#&#*#+#,#&#*#+#,#&#*#+#,#'#-#&#)#.s#,'#-#/#0#)s#,VS*s#[##DUS$#US+D*s#Y:4&$#US%&US,D*s#\s#*>%$#US-)US.D*s#_s#^s#.%$#VM,KVNDK's#h$#m#&#j#(I#YS/Is#ks#is#h#j#2s#m##"). Qed.
#[export] Hint Rewrite xloB_eqf : bceq.
Lemma xhiB_eqf : forall fk, xhiB (mkbc fk) = xhi fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_brange); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_srange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB_eqf)|] [|@e; @p; @z; @hi; @x; @n; @op; @a; @b; @sx; @lo; @e0; @k; @i; @o; @fk|] "#$3#*#C#1#$#(#'#%#2###0#&#)#3#5#7#8#:#@#?#<#=#-#.#;#>#A#B#C#D#E#/#4#9#6+#@$#3%#0%#2%#A&#4%#5%#B)US&S'UCH#IUM#UNIVOHHUC#k#$J#UPDUS(IVQH##K(#GVQHInO%HH$#%/I#$%#&#'#UDG)'GUS)HnC$/$#(3$#%$#%&##nC$0$#(4&#%$#%'##nC$1$#(5*#%$#%(###E(#FUKF)%FnC$6$#(:##%$#%-#*nC$7$#(;%#%$#%.##nC$8$#(<'#%$#%/###L(#EUFE)%EnC$=$#(A##%$#%4#1nC$>$#(B%#%$#%5##nC$?$#(s##'#%$#%6##nJ#$#$s#$D#+$#&;$#)1&#*#+#,*&#*#+#,*&#*#+#,*&#*#+#,*'#-#.#)#/#'#-#0#1#)#$KG%KG&KGnC$s#$$#(s#(##%$#%;#8nC$s#%$#(s#)%#%$#%<##nC$s#&$#(s#*'#%$#%=##$EF%EF&EFnC$s#*$#(s#.##%$#%A#>nC$s#+$#(s#/%#%$#%B##nC$s#,$#(s#0'#%$#%s####$LE%LE&LEnC$s#0$#(s#4##%$#%s#'#s#$nC$s#1$#(s#5%#%$#%s#(##nC$s#2$#(s#6'#%$#%s#)##nJ#$#$s#7D#+$#&s#.$#)/&#*#+#,)&#*#+#,)&#*#+#,)&#*#+#,)'#-#.#)#/#'#-#0#1#)#'s#86#j#2s#3#URDnC$s#7$#(s#;s#-#%$#%s#.#s#+nC$s#8$#(s#<8#%$#%s#/##nC$s#9$#(s#=s#2#%$#%s#0##nC$s#:$#(s#>s#(#%$#%s#1#s#.nC$s#;$#(s#?5#%$#%s#2##nC$s#<$#(s#@s#+#%$#%s#3##nC$s#=$#(s#As#$#%$#%s#4#s#1nC$s#>$#(s#B2#%$#%s#5##nC$s#?$#(s#Cs#'#%$#%s#6##nJ#$#$s#DD#+$#&s#;$#))&#*#+#,&&#*#+#,&&#*#+#,&&#*#+#,&'#-#.#)#/#'#-#0#1#)#'s#E#0j#2s#@#US#DnC$s#D$#(s#Hs#:#%$#%s#;#AnC$s#E$#(s#Is#3#%$#%s#<#<nC$s#F$#(s#Js#-#%$#%s#=#7nJ#$#$s#KD#+$#&s#B$#)%&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#0#1#)#'s#L#7j#2s#G#$GD%GD&GDnC$s#M$#(s#Q##%$#%s#D#s#AnC$s#N$#(s#R%#%$#%s#E##nC$s#O$#(s#S'#%$#%s#F##$FK%FK&FKnC$s#S$#(s#W##%$#%s#J#s#GnC$s#T$#(s#X%#%$#%s#K##nC$s#U$#(s#Y'#%$#%s#L##nJ#$#$s#ZI#+$#&s#Q$#))&#*#+#,#&#*#+#,#&#*#+#,#&#*#+#,#'#-#.#)#/s#,'#-#0#1#)s#,VS*s#[##DUS$#US+D*s#Y:4&$#US%&US,D*s#\s#*>%$#US-)US.D*s#_s#^s#.%$#VM,IVNDI's#h$#m#&#j#(J#YS/Js#ks#is#h#j#3s#m##"). Qed.
#[export] Hint Rewrite xhiB_eqf : bceq.
Lemma xt_nowrapB_eqf : forall fk, xt_nowrapB (mkbc fk) = xt_nowrap fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xt_nowrapB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xt_nowrap); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapRB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_nowrapR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapRB_eqf); constr:(@Corelib.Init.Datatypes.pair); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr) (@Corelib.Numbers.BinNums.Z))|] [|@ts; @l; @p; @b; @e; @IH; @rest; @k; @z; @a; @fk|] "##l#-#C###4#:#$#+#;#%#'#,#D#0#5#7#=#(#@#*#C#&#A#3#1#9#>#E#F#?#8#2#6#<#B(#/%#@$#A&#.%#B%UMS($CUN#UOCVS)EHUM#$I&#C#IC%D$#j#$'#US*)#F#VPD#$J&#C#JC%D$#$QWR1IF&$##Q$%D$#k##(#k#%5#j#&7#$S#&#C#S#C%D$##GF$KVS$#J'#CVLKJ#KI'$#%D&#j#'D#k#(EDULGUCJ'#)%D#)j#''#VLGS%'#2VPD#$GUS$#US+GZS&.-)&$#&&FZS&D91$#CXS,EHS%IWRs#5#F&*##G$%D$#m#(#j#)A#j#*s#:#j#+H#j#(E#V#FCj#,H#j#(E#YS-EHs#,#Cj#-s#B#YS.s#Cs#=s#:#Cj#$S'#YS/S'Ds#Gs#F#j#.s#J##"). Qed.
#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Lemma lin_ge0_scaledB_eqf : forall fk, lin_ge0_scaledB (mkbc fk) = lin_ge0_scaled fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0_scaledB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0_scaled); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_test); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_scale_need); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.has_srl); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_expand); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB_eqf)|] [|@ts; @test; @c; @t; @lo; @x; @c3; @t3; @c2; @t2; @b; @p; @x0; @fk|] "#$7#+#O#4#1###2#$#%#C#3#<#&#(#5#7#9#D#'#.#;#B#?#E#)#M#8#0#/#A#I#J#K#*#N#O#P#Q#6#=#@#H#G#L#>#F#:-#F$#G$#H$#I%#J%#K%#9%#L%#M'#N&US#S,VFDJUS##k#$#C#EUN#UOE#GVN#EVOGEk##DCk##D#k#%#Ck#$-#k#&D#UPH$GVS$K#US-S%%#%#%#US&#*)#nC#$##C)#%###I#L%S%US&#$H&$#WS.DJE'$#WS/DJE+DJ$#j#'s###XS's#$s#$#GVQ-#VFDs#%US0E#MVQ#E+Ds#)KEnC#$##'&#%#$##$M&3#'#S((#L(#G*KGj##D#j#(D#WR&E#nF%Ds#4$#)C,#$%#*#+#nF%Ds#5$#)C3#$%#,#-#nC#$##C@#%###I)L6)MEnC#$##65#%###2XPS1-E*nF%Ds#;$#)C$#$%#*#+#nF%Ds#<$#)C'#$%#,#-#nC#$##Cs#'#%###I,C*#j#.s#3#k#$s#@=US)HUEAUHEnC#$##A@#%###=nF%Ds#E$#)C##$%#*#+-nF%Ds#F$#)C&#$%#,#-#nC#$##Cs#1#%###I,C#-j#/+#$EVS$K#*$s#8nC#$##C$#%###I&s#5s#@'#s#3+DJ#s#2j#'s#R#XS's#Ss#S#E)H#)REnC#$##s#2s#1#%###s#.$R&s#>#'#M(#L(#GXPS(#Es#+nF%Ds#\$#)C)#$%#*#+#nF%Ds#]$#)C,#$%#,#-#nC#$##C3#%###IVS2C##HUQ#US3HZS*s#%s#$<&$#US4&US5HZS*s#Zs#Ys#)%$#WN)GEWOHGE,C$#m#&#j#0s#k#YS+s#lCs#fs#e#j#)D#YS+Ds#ms#ks#j#j#1s#q##"). Qed.
#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
Lemma lin_galignB_eqf : forall fk, lin_galignB (mkbc fk) = lin_galign fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_galignB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_galign); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.fold_right); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ctz64); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf)|] [|@ts; @e; @g; @t; @z; @x0; @x; @fk|] "##V#)#=#/###$#%#1#2#4#6#,#7#.#-#0#<#=#(#'#>#?#@#5#3#;#:#9#8(#8$#9$#:%#;%#<(UKNVOCGUK#k#$#C#DUH#UID#EVH#DVIEDk#%GCUJFWPCGE$#WQCGEUF#%%#&D#j#&C#j#'4#$F'C6$#EVJR*%,#&D#j#&C#j#';#'C<#)EWLC)#j#(5#VJS#2%4#&D#j#&C#j#'s###$E'Cs#%$#DVS$C##FUS%#US&FZS'A@.&$#WH&EDWIFEDWLC$#m#&#j#)s#.#YMs#/Cs#)s#(#j#*C#YMCs#0s#.s#-#j#+s#4##"). Qed.
#[export] Hint Rewrite lin_galignB_eqf : bceq.
Lemma lin_ge0_alB_eqf : forall fk, lin_ge0_alB (mkbc fk) = lin_ge0_al fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0_alB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0_al); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_galign); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_test); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_expand); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_galignB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_galignB_eqf)|] [|@ts; @c; @lo; @x; @c2; @t2; @z; @test; @b; @p; @x0; @fk|] "#$P#+#M#4#1#$#%###&#2#'#(#E#H#5#7#<#A#)#J#.#9#@#F#G#I#0#/#3#*#K#L#M#N#O#=#D#C#B#6#?#:#>#;#8/#C%#D%#E%#F%#5&#G$#H$#9'#I&#J$#K%#L)US$S+VIDS,US$#k#$#C(GUN#UOG(EVN#GVOEGk#$*Dk#%D#US%FVGFE)S&)#)#)#,##(#-P#(H,S&,+VFJH##)$%#%'#&#Ej##D#j#&D#XQ,FE#VS'-E(KVS(JEVJRK##4$0#%2#&#Ej##D#j#&D#XQ+*G#nI%Ds#+$#'C-#$%#(#)#nC#$##C/#%#L##nC#$##C;#%###M'HFE##?-P#'KJH##B$>#%@#&#Ej##D#j#&D#*HFE#VS#HE'S-RK##s#+$s#'#%s#)#&#Ej##D#j#&D#*KAG#nI%Ds#B$#'C+#$%#(#)#nC#$##C-#%#L##nC#$##C6#%###M+C:#j#*s#=#k##DCk##D#k#+#Ck#$s#J#k#%D#US)FWGFE8WFs#.G0nI%Ds#O$#'Cs#1#$%#(#)#nC#$##C%#%#L##nC#$##Cs###%###M+C#0j#,*#VIDs#Tk#$s#U#US#FUGEnI%Ds#X$#'C##$%#(#)9nC#$##Cs###%#L##nC#$##Cs#,#%###M+C#9j#-)#'FEG##s#N-P#'JHF##s#Q$s#M#%s#O#&#Ej##D#j#&D#*FEG#VS#FGVS(HE'RKJ##s#[$s#W#%s#Y#&#Ej##D#j#&D#*J*G#nI%Ds#r$#'C,#$%#(#)#nC#$##C.#%#L##nC#$##C7#%###MVS.C#(FUS'#US/F.s#&s#%?&$#UQ&US0F.s#3s#2s#+%$#US1)US2F.s#vs#us#;%$#WN,EGWOFEG+C$#m#&#j#.s$(#YS*s$)Cs$#s#~#j#'D#YS*Ds$*s$(s$'#j#/s$.##"). Qed.
#[export] Hint Rewrite lin_ge0_alB_eqf : bceq.
Lemma lin_ge0B_eqf : forall fk, lin_ge0B (mkbc fk) = lin_ge0 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0_al); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xt_nowrapB); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xt_const); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lsub_e); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xt_lin); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.has_srl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0_scaledB); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xt_nowrap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_test); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.srl_expand); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0_scaled); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.srl_expandB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_testB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xt_nowrapB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0_scaledB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0_alB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0_alB_eqf)|] [|@neg; @ts; @c; @lo; @x; @c3; @t3; @c2; @t2; @b; @test; @p; @x0; @fk|] "#%##+#S#2#E###%#7#$#8#=#&#'#1#(#3#5#:#<#F#N#.#*#)#I#K#L#M#>#0#/#9#C#D#H#O#P#Q#R#S#T#U#@#4#?#G#;#B#6#A#J1#J$#K$#L%#M%#:'#N&#O$#P)#Q%#9%#R%#;%#<'#%$US%S.k#$MC$EUO#UPE$HVO#EVPHEVIGS/US%#k#%#Ck#&G#UQF$KVR#FVR$HnC#$##C$#%###J#F#H%$#)F)H+$#VS0S1Hj##G#j#'G#//)&#VS#0'$N#L#K%$#&#H/'#E*US2EVS#)E$S&#S'#N%$#&#K&#H/(#E3nI%Gs#$$#(C*#$%#)#*#nC#$##C,#%###J)L)K+$#WS(63#VF4$nC#$##C$#%#D##nC#$##C)#%#D##nC#$##C5#%#D##nI%Gs#.$#(C<#$%#+#,#nC#$##C>#%#D##nC#$##Cs#)#%###J,KF,KH-$#'Ks#*s#'s#$.Ks#('N?Es#&.NE'S&8Es#(nI%Gs#9$#(C$#$%#)#*#nC#$##CA#%###JWS$Ns#%5WQNs#&6nC#$##C$#%#D##nC#$##C&#%#D##nC#$##C+#%#D##nI%Gs#@$#(C-#$%#+#,#nC#$##C/#%#D##-1#(C5#j#-s#B#US$FnC#$##C>#%#D#,nC#$##Cs#$#%#D##nC#$##Cs#0#%#D##nI%Gs#I$#(Cs#7#$%#+#,#nC#$##Cs#9#%#D##nC#$##Cs#D#%###J(C#,j#-s#K#k#%MCUS)F0F0HnC#$##C$#%###JnC#$##Cs#0#%#D#8nC#$##Cs#<#%#D##nI%Gs#U$#(Cs#C#$%#+#,#nC#$##Cs#E#%#D##nC#$##C'#%###J(C#8j#--#k##GCk##G#k#.#Ck#%s#]#k#&G#US*FnC#$##Cs#1#%#s#0#JWEs#Ws#Ts#QWFs#KEs#RWLs#CEs#SnI%Gs#d$#(Cs#J#$%#)#*#nC#$##Cs#L#%###JnC#$##C##%#D#s#+nC#$##C'#%#D##nI%Gs#h$#(Cs#V#$%#+#,#nC#$##C*#%#D##nC#$##C,#%###J(C#s#+j#-0#VIGs#mk#%s#n#US+F0s#cUFEnI%Gs#r$#(C##$%#)#*s#<nC#$##Cs#Z#%###JnC#$##C##%#D#s#9nC#$##Cs#A#%#D##nI%Gs#v$#(C(#$%#+#,#nC#$##Cs#E#%#D##nC#$##C:#%###J(C#s#9j#/.#,FH,FE-$##E%s#v#)E+s#u#'F%#s#r.F$%s#os#|&#H'L#Es#v.LE%s#ks#t&#K&#H'S'#Es#{nI%Gs$0$#(C'#$%#)#*#nC#$##Cs#t#%###J+s#is$'WS$L-#WQL.$nC#$##C$#%#D##nC#$##C'#%#D##nC#$##C/#%#D##nI%Gs$8$#(C3#$%#+#,#nC#$##C5#%#D##-;#VS3C#$FUS##US4F*s#/s#.s##&$#US,&US5F*s#Bs#As#4%$#UR)US6F*s#Us#Ts#J%$#US(,US7F*s$Fs#as#Y%$#US8/US9F*s$Is$Hs#e%$#WO2HEWPFHE(C$#m#&#j#0M#YS-MCs$Ts$S#j#(M#YS-Ms$[s$Ys$X#j#1s$]##"). Qed.
#[export] Hint Rewrite lin_ge0B_eqf : bceq.
Lemma xinside0B_eqf : forall fk, xinside0B (mkbc fk) = xinside0 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinside0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf)|] [|@n2; @k2; @b2; @n1; @k1; @neg; @pos; @b; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##u#+#A#1###2#$#3#%#&#'#4#6#)#(#?#@#8#9#*#:#.#/#<#>#A#B#C#7#;#=#5#0(#=&#>'#?$#@(#2&US%S&k#$CGk#%E#k#&C#k#'C#k#(E#%DUK#ULD%FVK#DVLFD%HWK#FDWLHFD%IXK#HFDXLIHFD%JYK#IHFDYLJIHFD%NZK#JIHFDZLNJIHFDk#)QGk#*Q#URMVS'CE$CEMNUS($#%$#$CEIH#'#%VD%#$CEFO#*#(#+'#$CEJO#-#+#.-#VD&#nG#$##G*#%###P'S#.,'S#)&nG#$##G$#%###PWS$G&#j#+7#$CENJ#7#5$CEHF#9#7'M%#$CEDO#<#:#='#$CEIO#?#=#@,#'M&#nG#$##G*#%###PVS)G#%MUS*#US+MZS,s#)s#(4&$#[K&NJIHFD[LMNJIHFDWS$G$#m#&#j#,C#&CGs#2s#1#j#-E#&Es#Is#7s#6#j#.C#&Cs#Js#<s#;#j#/C#&Cs#Ks#As#@#j#0E#&Es#Ls#Fs#E#j#1C#&Cs#Ms#Ks#J#j#2s#S##"). Qed.
#[export] Hint Rewrite xinside0B_eqf : bceq.
Lemma xinside_numB_eqf : forall fk, xinside_numB (mkbc fk) = xinside_num fk.
Proof. intros. bcfe. unfold xinside_numB, xinside_num. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside_numB_eqf : bceq.
Lemma xinsideB_eqf : forall fk, xinsideB (mkbc fk) = xinside fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside_num); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.shares_var); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinside0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.novars); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside0); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinside0B_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinside_numB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinside_numB_eqf)|] [|@n2; @k2; @b2; @n1; @k1; @b1; @b; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##w#+#A#3#$#%###&#'#)#1#(#>#4#6#2#=#8#*#?#:#;#7#.#/#@#A#B#C#5#0#<#9'#=$#>(#?$#@&US'S(k#$JCk#%O#k#&J#k#'J#k#(O##FUM#UNF#DVM#FVNDF#EWM#DFWNEDF#GXM#EDFXNGEDF#HYM#GEDFYNHGEDF#KZM#HGEDFZNKHGEDFk#)J5UQIVS$IG#R[S%#IKHGED%GZFIKHGED%HnC#$##C##%#L#&nC#$##C%#%#P##nC#$##C'#%###LnC#$##C+#%#)##[S#RIKHGED[QRIKHGEDnC#$##C)#%#L#$nC#$##C$#%#P##nC#$##C-#%###LnC#$##C1#%#'##&C)#j#*5#US#InC#$##C0#%#L#1nC#$##C+#%#P##nC#$##C4#%###LnC#$##C8#%#4##&C#*j#*<#VS$KE[S#IKHGEDF%E[QIKHGEDFnC#$##C<#%#L#%nC#$##C$#%#P##nC#$##C&#%###LnC#$##C)#%#(##VS)C##IUS%#US*IZS&s#)5/&$#US+&US,IZS&s#,s#+9%$#[M)KHGEDF[NIKHGEDF&C$#m#&#j#+J#$JCs#4s#3#j#,O#$Os#Ks#9s#8#j#-J#$Js#Ls#>s#=#j#.J#$Js#Ms#Cs#B#j#/O#$Os#Ns#Hs#G#j#0J#$Js#Os#Ms#L#j#1s#U##"). Qed.
#[export] Hint Rewrite xinsideB_eqf : bceq.
Lemma sub_itvB_eqf : forall fk, sub_itvB (mkbc fk) = sub_itv fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itvB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xlo); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf)|] [|@m; @c; @n; @k; @n2; @k2; @b2; @n1; @k1; @b1; @x; @ml; @b; @e; @o; @x3; @x2; @x1; @x0; @fk|] "#$3#*#J#3###$#>#1#%#&#(#'#0#4#6#A#B#2#8#)#H#;#:#?#C#D#E#F#7#-#.#I#J#K#L#5#<#/#@#G#=#9*#C$#D%#E(#F%#G%#H$#I&US-S.k#$LCk#%Q#k#&G#k#'G##DUM#UND#EVM#DVNED#HWM#EDWNHED#IXM#HEDXNIHED#KYM#IHEDYNKIHEDk#(LCk#)G#k#*L#k#+L#k#,G#k#-L#URJUS%HVS&J#(H$#KnC#$##C%#%###F#S#VS'#E&JK(I&#D$%#nO$G$#.C'#%$#/##FnC#$##C*#%###F$S(IVS)IS*nC#$##C$#%###FUS+IZDJK#31EnC#$##C%#%###FnC#$##C)#%#P##'53VS$S#EnO$G$#.C##%$#/.#FnC#$##C%#%###F'-,[RS#JK+;9EnC#$##C$#%###FnC#$##C&#%#P##)C+#j#0A#UOGk#1L#US$JUDEnO$G$#.C##%$#/:#FnC#$##CA#%###FnC#$##C7#%#-#FnC#$##C$#%#P##)C#-j#2*#US%EVS&K#(E$#I'%#VS$JD&KI&s#/D$$#nO$G$#.C&#%$#/##FnC#$##C(#%###F$S(HVS)HS*'$#US+H[RJKI#1/DnC#$##C%#%###FnC#$##C)#%#P##VS/C##JUS'#US0JZS,A@9&$#US1&US2JZS,s#Es#Ds#&%$#ZM)KIHEDZNJKIHED)C$#m#&#j#3L#%LCs#Rs#Q#j#4Q#%Qs#es#Ws#V#j#5G#%Gs#fs#\s#[#j#6G#%Gs#gs#as#`#j#.L#%Ls#hs#fs#e#j#7s#m##"). Qed.
#[export] Hint Rewrite sub_itvB_eqf : bceq.
Lemma kdisj_apartB_eqf : forall fk, kdisj_apartB (mkbc fk) = kdisj_apart fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kdisj_apartB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kdisj_apart); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itvB); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itvB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@n2; @k2; @b2; @n1; @k1; @b1; @kn; @k; @a; @w; @v; @n; @k0; @lo; @hi; @e; @m; @c1; @m1; @c2; @m2; @c; @b; @IH; @rest; @K; @fk|] "#$[#9#M#A#%###&#$#@#(#'#)#?#*#,#+#=#B#D#-#K#L#8#3#7#1#G#2#M#J#I#<#H#0#.#6#/#N#5#O#P#E#C#>#F+#J$#2+#<)#K(#L&#1+#=)#*(US/Pk#$HCk#%H#k#&L#k#'H#k#(H#k#)L##EUQ#URE#GVQ#EVRGE#DWQ#GEWRDGE#FXQ#DGEXRFDGE#JYQ#FDGEYRJFDGE#IZQ#JFDGEZRIJFDGE#K[Q#IJFDGE[RKIJFDGE#S)(#KIJFDGE$S)KIJFDGE'C$#k#$H#k#%H#k#&L#k#'H#k#(H#k#)L#j#*s#(#US0P$S1#IJFDGEVS*C#j#$H#j#%H#j#&L#j#'H#j#(H#j#)L##S+(#KIJFDGE$S+KIJFDGE'C$#k#$H#k#%H#k#&L#k#'H#k#(H#k#)L#$S'MIJFDGE#S&)#S#NOFD)$MKIGEnC#$##C$#%###S$)&S#NOGE)'MKIFDnC#$##C$#%###S$nC#$##C##%#S%#JnC#$##C'#%#S%##nP#$#+CN#-&#,#-#.F%#,#/D&#,#/#0F%#1#2D%#3#4D&#3#1#2F%#,#/D'#5#6#7#8#&#,#/#9F%#,#/D$S(S2NOMKIJ$S3S#OMKIJF%S&S#NOFD%S&MKIGEnC#$##C$#%###S$%S&S#NOGE%S&MKIFDnC#$##C$#%###S$$S&S4S#NOMKInC#$##C$#%#S%##nC#$##C(#%#S%##nP#$#+CN#-&#,#-#.-%#,#/,&#,#/#0-%#1#2,%#3#4,&#3#1#2-%#,#/,'#5#6#7#8#&#,#/#9-%#,#/,'C/#j#:C#k#4LCk#9S5#k#/H#k#+H#k#:L#US,S'*S#NOFD*MKIGEnC#$##C$#%###S$*S#NOGE*MKIFDnC#$##C$#%###S$nC#$##C##%#S%#4nC#$##C'#%#S%##nP#$#+CN#-&#,#-#.>%#,#/=&#,#/#0>%#1#2=%#3#4=&#3#1#2>%#,#/='#5#6#7#8#&#,#/#9>%#,#/='C#4j#:.#$S6NMKIJFD%S(NOMFD%S(KIJGEnC#$##C$#%###S$%S(NOMGE%S(KIJFDnC#$##C$#%###S$nC#$##C##%#S%#s#(nC#$##C'#%#S%##nP#$#+CO#-&#,#-#.s#)%#,#/+&#,#/#0s#)%#1#2+%#3#4+&#3#1#2s#)%#,#/+'#5#6#7#8#&#,#/#9s#)%#,#/+VS*C##S'US-#US7S'ZS.=<1&$#(&MIJFDGEZKIJFDGEZS.Cs#=s#%%$#WS8POM(*#IJFDGE$S'$IJFDGE'C$#m#'#j#$H#j#%H#j#&L#j#'H#j#(H#j#)L#j#;s#J#j#<s$(#j#=P#_S9Ps#`s#W#KIJFDGEj#$H#&HCs#ns#m#j#%H#&Hs$-s#ss#r#j#&L#&Ls$.s#xs#w#j#'H#&Hs$/s#}s#|#j#(H#&Hs$0s$&s$%#j#)L#&Ls$1s$+s$*#j#*s$7#&s$8s$2s$0s$/#j#>s$9##"). Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma ranges_apartB_eqf : forall fk, ranges_apartB (mkbc fk) = ranges_apart fk.
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Lemma sub_itv_xB_eqf : forall fk, sub_itv_xB (mkbc fk) = sub_itv_x fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itv_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv_x); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf)|] [|@m; @c; @n; @k; @n2; @k2; @b2; @n1; @k1; @b1; @b; @x3; @x2; @x1; @x0; @x; @fk|] "##[#*#<###$#0#%#&#'#(#3#4#6#1#2#8#:#;#9#-#.#)#<#=#>#7#5#/%#:$#;(US#S$k#$EJk#%N#k#&E#k#'M##CUK#ULC#DVK#CVLDC#FWK#DCWLFDC#GXK#FDCXLGFDC#HYK#GFDCYLHGFDCk#(EJk#)M#k#*E#k#+E#k#,M#k#-E#UOIUPFUQFZCIHG$#D[OS%IHG%$DWRJ$#j#.)#UPDUQD[OIHGF$#CVS&J##IUS'#US(IZS)10*&$#ZK&HGFDCZLIHGFDCWRJ$#m#&#j#/E#$EJ>=#j#0N#$Ns#1s##B#j#1E#$Es#2s#(s#'#j#2M#$Ms#3s#-s#,#j#3E#$Es#4s#2s#1#j#4s#9##"). Qed.
#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Lemma kdisj_apart_xB_eqf : forall fk, kdisj_apart_xB (mkbc fk) = kdisj_apart_x fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kdisj_apart_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kdisj_apart_x); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itv_xB); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv_x); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itv_xB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@n2; @k2; @b2; @n1; @k1; @b1; @kn; @k; @a; @w; @v; @n; @k0; @lo; @hi; @e; @m; @c1; @m1; @c2; @m2; @c; @b; @IH; @rest; @K; @fk|] "#$[#9#M#A#%###&#?#$#(#'#)#@#*#,#+#=#B#D#-#K#L#8#3#7#1#G#2#M#J#I#<#H#0#.#6#/#N#5#O#P#E#C#>#F+#J$#2+#<)#K(#L&#1+#=)#*(US/Pk#$GCk#%L#k#&G#k#'G#k#(L#k#)G##EUQ#URE#HVQ#EVRHE#DWQ#HEWRDHE#FXQ#DHEXRFDHE#JYQ#FDHEYRJFDHE#IZQ#JFDHEZRIJFDHE#K[Q#IJFDHE[RKIJFDHE#S)(#KIJFDHE$S)KIJFDHE'C$#k#$G#k#%L#k#&G#k#'G#k#(L#k#)G#j#*s#(#US0P$S1#IJFDHEVS*C#j#$G#j#%L#j#&G#j#'G#j#(L#j#)G##S+(#KIJFDHE$S+KIJFDHE'C$#k#$G#k#%L#k#&G#k#'G#k#(L#k#)G#$S'MIJFDHE#S&)#S#NOFD)$MKIHEnC#$##C$#%###S$)&S#NOHE)'MKIFDnC#$##C$#%###S$nC#$##C##%#S%#JnC#$##C'#%#S%##nP#$#+CN#-&#,#-#.F%#,#/D&#,#/#0F%#1#2D%#3#4D&#3#1#2F%#,#/D'#5#6#7#8#&#,#/#9F%#,#/D$S(S2NOMKIJ$S3S#OMKIJF%S&S#NOFD%S&MKIHEnC#$##C$#%###S$%S&S#NOHE%S&MKIFDnC#$##C$#%###S$$S&S4S#NOMKInC#$##C$#%#S%##nC#$##C(#%#S%##nP#$#+CN#-&#,#-#.-%#,#/,&#,#/#0-%#1#2,%#3#4,&#3#1#2-%#,#/,'#5#6#7#8#&#,#/#9-%#,#/,'C/#j#:C#k#4GCk#9S5#k#/G#k#+L#k#:G#US,S'*S#NOFD*MKIHEnC#$##C$#%###S$*S#NOHE*MKIFDnC#$##C$#%###S$nC#$##C##%#S%#4nC#$##C'#%#S%##nP#$#+CN#-&#,#-#.>%#,#/=&#,#/#0>%#1#2=%#3#4=&#3#1#2>%#,#/='#5#6#7#8#&#,#/#9>%#,#/='C#4j#:.#$S6NMKIJFD%S(NOMFD%S(KIJHEnC#$##C$#%###S$%S(NOMHE%S(KIJFDnC#$##C$#%###S$nC#$##C##%#S%#s#(nC#$##C'#%#S%##nP#$#+CO#-&#,#-#.s#)%#,#/+&#,#/#0s#)%#1#2+%#3#4+&#3#1#2s#)%#,#/+'#5#6#7#8#&#,#/#9s#)%#,#/+VS*C##S'US-#US7S'ZS.=<1&$#(&MIJFDHEZKIJFDHEZS.Cs#=s#%%$#WS8POM(*#IJFDHE$S'$IJFDHE'C$#m#'#j#$G#j#%L#j#&G#j#'G#j#(L#j#)G#j#;s#J#j#<s$(#j#=P#_S9Ps#`s#W#KIJFDHEj#$G#&GCs#ns#m#j#%L#&Ls$-s#ss#r#j#&G#&Gs$.s#xs#w#j#'G#&Gs$/s#}s#|#j#(L#&Ls$0s$&s$%#j#)G#&Gs$1s$+s$*#j#*s$7#&s$8s$2s$0s$/#j#>s$9##"). Qed.
#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Lemma end_hiB_eqf : forall fk, end_hiB (mkbc fk) = end_hi fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.end_hiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.end_hi); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.find_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.facts_of); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.find_rangeI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_ri); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.find_rangeI_mkbc)|] [|@h1; @hi1; @lo1; @n; @k; @e; @p; @z; @ehi; @x; @n0; @op; @a; @b0; @sx; @lo; @k0; @i; @o; @x4; @x3; @x2; @x1; @x0; @fk|] "#$N#/#M#6#A###$#&#'#%#(#)#7#I#5#8#:#*#+#C#F#G#,#<#=#-#?#2#3#@#K#.#L#N#M#O#;#D#H#9#>#4#B#E#J,#E%#F&#G$#H$#I(#J%#K%#L$#8%US+S,ULCk#$C#k#%C#k#&C#k#'N#k#(C#%EUO#UPE%FVO#EVPFE%IWO#FEWPIFE%GXO#IFEXPGIFE%HYO#GIFEYPHGIFE%JZO#HGIFEZPJHGIFEVS'CCUL#k#)N#&KUS(#US-C#HK(S###GK##I)#S$nD#$##D&#%###S%*K$MQ#$M#JUF#VS.CEnS'%CC$#*s#+E#$%#+#,#nL$4$#-s#,%#%$#*##/nD#$##s#-*#%###0#KR(S###JR##H)#S$nD#$##D&#%###S%*R$MS&#$M#QUG#nL$@$#-s#8##%$#*/#;nD#$##s#9(#%###<#QS&(S###KS&##J)#S$nD#$##D&#%###S%*S&$MS)#$M#RUH#nL$s#,$#-s#D##%$#*;#s#'nD#$##s#E(#%###s#(nN#$#'s#FH#+$#+s#)$#.;&#/#0#1/&#/#0#1/&#/#0#1/&#/#0#1/'#2#3#.#)#'#2#4#5#.#&R+#BnL$s#1$#-s#I##%$#*@#s#,nD#$##s#Js#'#%###s#-&S)+#8nL$s#5$#-s#M##%$#*s#$#s#0nD#$##s#N=#%###s#1&S/+#0nL$s#9$#-s#Q##%$#*s#(#s#4nD#$##s#R5#%###s#5nN#$#'s#SH#+$#+s#6$#.+&#/#0#1'&#/#0#1'&#/#0#1'&#/#0#1''#2#3#.#)#'#2#4#5#.#WS*s#T0#j#6s#;##GJ(S###IJ##F)#S$nD#$##D&#%###S%&Q*J$MK#$M#H+&#nL$s#I$#-s#a##%$#*s#8#s#DnD#$##s#b)#%###s#E#JQ(S###HQ##G)#S$nD#$##D&#%###S%&S&*Q$MR#$M#K+&#nL$s#V$#-s#n##%$#*s#E#s#QnD#$##s#o)#%###s#RnN#$#'s#pG#+$#+s#S$#.0&#/#0#1#&#/#0#1#&#/#0#1#&#/#0#1#'#2#3#.#)s#$'#2#4#5#.s#$VS0s#q#%KUS1#US2#US3KZS4s#\s#Zs##'$#[O'JHGIFE[PKJHGIFEWS*s#y$#m#&#j#7C#'Cs#|s#fs#e#j#8C#'Cs#}s#ks#j#j#9C#'Cs#~s#ps#o#j#:N#'Ns$#s#us#t#j#;C#'Cs$$s#zs#y#j#-N#'Ns$%s$#s#~#j#<s$,##"). Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : forall fk, ranges_apart_xB (mkbc fk) = ranges_apart_x fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_x); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.end_hi); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apartB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kdisj_apart_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.shares_var); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kdisj_apart_x); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apartB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kdisj_apart_xB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.end_hiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.end_hiB_eqf)|] [|@n2; @k2; @b2; @n1; @k1; @h1; @hi1; @lo1; @n; @k; @b; @x; @e1; @e2; @h2; @p0; @lo2; @hi2; @p; @z2; @op; @a; @sx; @lo; @e; @i; @z1; @o; @b1; @kn; @neg; @pos; @l; @x4; @x3; @x2; @x1; @x0; @fk|] "#+<#8#g#@#?#P#E#O###)#J#>#(#*#'#%#&#+#,#-#.#$#/#2#0#1#3#4#5#Y#A#C#6#Z#F#I#H#7#^#`#_#\#[#K#L#U#Q#;#<#X#a#b#c#d#e#f#g#h#i#N#V#M#B#W#G#D#R#T#S#]#=9#[%#\&#]%#^$#_'#F+#J%#I%#B*#H&#K%#L%#M&#`&#a)#b$#c%#d$#e%#f(#N+#1$US?S@k#$KCk#%D#k#&K#k#'K#k#(D#&HUS.#US/H&S%VS.#HVS/S%H&OWS.#S%HWS/OS%H&PXS.#OS%HXS/POS%H&NYS.#POS%HYS/NPOS%H&LZS.#NPOS%HZS/LNPOS%HUFDk#)D#k#*D#k#+D#k#,K#k#-D#k#.K#US2I&RUS3S%US3H[S4%QM$LN#VJDD-'Q&S&-#Q&S'.#S&&S*.#S##LS'##S%#PS&%$##OS&##H#IS'%$#nC#$##C'#%#G##ZS#S*S'S)ILS%#NS(%H#nF$D$#/C%#%$#0##EZS#S(S&S$POH#MS*%H#nF$D$#/C%#%$#1##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#/C6#%$#2##EnF$D$#/C9#%$#)##EnJ%DD$#3CH#$%#4#5#nF$@$#/C=#%$#3##EnJ%DD$#6CH#$%#+#*#nF$B$#/CA#%$#6##E2s#'7s#(#QMILNP3QL4#VJKD'KDLNUSA$$%$#'KDQM'KDIS-$(#&$)%#/s#3'#$+')'KDPS-$-#+$.-#/s#8&#nC#$##C(#%#G##nC#$##C2#%#E##nC#$##C5#%#G##nC#$##C8#%#G##&S$-#S#&S)-#S#&S+.#S)&S,.#S&#LS+##S%#PS)%$##OS)##H#IS+%$#nC#$##C'#%#G##ZS&S,S+S*ILS%#NS'%H#nF$D$#/C%#%$#0##EZS&S'S)S(POH#MS,%H#nF$D$#/C%#%$#1##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#/C6#%$#2##EnF$D$#/C9#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s#W$#/C=#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s#Y$#/CA#%$#6##E2s##7s#$#S#RQMIL3S#M4#'KDMI$s#:#s#8'KDS#R'KDQS-$s#=#s#;$s#>%#/s#-'#$s#@'s#>'KDLS-$s#B#s#@$s#C,#/s#2&#nC#$##C(#%#G##nC#$##C0#%#E##nC#$##C3#%#G##nC#$##C6#%#G##-s#lS$-s#kS$.s#3S'&S0.#S(#LS,##S%#PS'%$##OS'##H#IS,%$#nC#$##C'#%#G##ZS(S0S,S+ILS%#NS*%H#nF$D$#/C%#%$#0##EZS(S*S'S)POH#MS0%H#nF$D$#/C%#%$#1##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#/C6#%$#2##EnF$D$#/C9#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s$-$#/C<#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s$/$#/C?#%$#6##E2s$.7s$/#S$S#RQMI3S$Q4#'KDS$S#'KDRS-$s#m#s#k$s#n%#/s$6s#f#$s#p's#n/s$8#s#jnC#$##C%#%#G##nC#$##C+#%#E##nC#$##C.#%#G##nC#$##C1#%#G##nK#$#$CO#+$#7s$@$#,s#e&#8#9#.s#0&#8#9#.s#0&#8#9#.s#0&#8#9#.s#0'#:#;#,#<#'#:#-#=#,#&Q-#M-s#gM.s#fS$.s$@R#LS)##S%#PS$%$##OS$##H#IS)%$#nC#$##C'#%#G##ZRS'S)S(ILS%#NS&%H#nF$D$#/C%#%$#0##EZRS&S$S#POH#MS'%H#nF$D$#/C%#%$#1##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#/C6#%$#2##EnF$D$#/C8#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s$[$#/C;#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s$]$#/C>#%$#6##E2@7A#MILNPO3MN4#'KDNP$s$>#s$</s#&#s#Z'KDOS-$s$A#s$?$s$B'#/s#*s#g#nC#$##C'#%#G##nC#$##C+#%#E##nC#$##C.#%#G##nC#$##C1#%#G##&S#-#R&S(-#R.s$kS(.s$7S$#LS*##S%#PS(%$##OS(##H#IS*%$#nC#$##C'#%#G##ZS$S+S*S'ILS%#NS)%H#nF$D$#/C%#%$#0##EZS$S)S(S&POH#MS+%H#nF$D$#/C%#%$#1##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#/C6#%$#2##EnF$D$#/C8#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s%-$#/C;#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s%/$#/C?#%$#6##E2A7B#RQMILN3RI4#'KDIL$s$l#s$j'KDRQ'KDMS-$s$o#s$m$s$p%#/s#+'#$s$r's$p'KDNS-$s$t#s$r$s$u,#/s#0&#nC#$##C(#%#G##nC#$##C0#%#E##nC#$##C3#%#G##nC#$##C6#%#G##nK#$#'CN#+$#>s#c$#,s#6&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<s$5'#:#-#=#,s$5[S1RQMs%HLNs%G)RQ)S&Q*S'S&*S*S#5s%?s%;+S+S*S'S)ILS%nF$D$#/C##%$#0s%9#E+S+S(S&S$POHnF$D$#/C##%$#1s%7#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#/C*#%$#2##EnF$D$#/C,#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s%T$#/C/#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s%V$#/C2#%$#6##E(RRQMILNP,Rs%0s%,,Rs%+s%(nC#$##C$#%#G##nC#$##Cs%7#%#E##nC#$##C'#%#G##nC#$##C)#%#G##)S$S#)S)S#*S+S)*S,S&5s$|s$x+S0S,S+S*ILS%nF$D$#/C##%$#0s$v#E+S0S'S)S(POHnF$D$#/C##%$#1s$t#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#/C*#%$#2##EnF$D$#/C,#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s%l$#/C/#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s%n$#/C2#%$#6##E(S$S$S#RQMIL,S$s$os$k,S$s$js$gnC#$##C$#%#G##nC#$##Cs$t#%#E##nC#$##C'#%#G##nC#$##C)#%#G##)S&S$)S'S$*S,S'*S0S(5s$bs$^+S5S0S,S+ILS%nF$D$#/C##%$#0s$\#E+S5S*S'S)POHnF$D$#/C##%$#1s$Z#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#/C*#%$#2##EnF$D$#/C,#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s&($#/C/#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s&*$#/C2#%$#6##E(S&S&S$S#RQMI,S&s%Zs$S,S&s$Rs%]nC#$##C$#%#G##nC#$##Cs$Z#%#E##nC#$##C'#%#G##nC#$##C)#%#G##nK#$#$CO#+$#7s#K$#,s#3&#8#9#.;&#8#9#.;&#8#9#.;&#8#9#.;'#:#;#,#<#'#:#-#=#,#)QM)S$M*S)S$*S'R5s$Ms$I+S*S'S)S(ILS%nF$D$#/C##%$#0s$G#E+S*S&S$S#POHnF$D$#/C##%$#1s$E#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#/C*#%$#2##EnF$D$#/C,#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s&A$#/C/#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s&C$#/C2#%$#6##E(QQMILNPO,Qs$@s%;,Qs%Es$=nC#$##C$#%#G##nC#$##Cs$E#%#E##nC#$##C'#%#G##nC#$##C)#%#G##)S#R)S(R*S*S(*S+S$5s$7s$3+S,S+S*S'ILS%nF$D$#/C##%$#0s$1#E+S,S)S(S&POHnF$D$#/C##%$#1s$/#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#/C*#%$#2##EnF$D$#/C,#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s&Y$#/C/#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s&[$#/C2#%$#6##E(S#S#RQMILN,S#s$*s$&,S#s$%s#~nC#$##C$#%#G##nC#$##Cs$/#%#E##nC#$##C'#%#G##nC#$##C)#%#G##nK#$#'CN#+$#>s#3$#,;&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<s#L'#:#-#=#,s#L0Cs#~#j#?s&k#k#@Ks')k#As'/#US6InC#$##Cs&Y#%#G#s#xnF$D$#/Cs&c#%$#2##EnF$D$#/Cs&f#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s&m$#/Cs&j#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s&o$#/Cs&n#%$#6##E[Os&OQMILNPnC#$##C##%#G#s&=nC#$##C%#%#G##nC#$##Cs&,#%#G#s#jnF$D$#/Cs&6#%$#2##EnF$D$#/Cs&9#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s&w$#/Cs&=#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s&y$#/Cs&A#%$#6##E[Ns%~S#RQMILnC#$##C##%#G#s%nnC#$##C%#%#G##nC#$##Cs%`#%#G#s#\nF$D$#/Cs%j#%$#2##EnF$D$#/Cs%m#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s'%$#/Cs%p#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s''$#/Cs%s#%$#6##E[Ls%VS$S#RQMInC#$##C##%#G#s%KnC#$##C%#%#G##nK#$#$CO#+$#7s',$#,7&#8#9#.-&#8#9#.-&#8#9#.-&#8#9#.-'#:#;#,#<#'#:#-#=#,#nC#$##Cs%=#%#G#s#NnF$D$#/Cs%G#%$#2##EnF$D$#/Cs%I#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s'0$#/Cs%L#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s'2$#/Cs%O#%$#6##E[S%s%3MILNPOnC#$##C##%#G#s%(nC#$##C%#%#G##nC#$##Cs$u#%#G#s#@nF$D$#/Cs%##%$#2##EnF$D$#/Cs%%#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s':$#/Cs%(#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s'<$#/Cs%,#%$#6##E[Ps$kRQMILNnC#$##C##%#G#s$[nC#$##C%#%#G##nK#$#'CN#+$#>7$#,-&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<B'#:#-#=#,B0C#s#<j#.s#9#k#$DCk#%D#k#&K#k#'D#k#(D#k#@K#US1IZOQMs'MLNs'L(Rs'*QMILNPnC#$##C##%#G#s&tnC#$##Cs#<#%#G##(S$s&RS#RQMILnC#$##C##%#G#s&BnC#$##Cs#5#%#G##(S&s&#S$S#RQMInC#$##C##%#G#s%tnC#$##Cs#.#%#G##nK#$#$CO#+$#7,$#,)&#8#9#.&&#8#9#.&&#8#9#.&&#8#9#.&'#:#;#,#<#'#:#-#=#,#(Qs%UMILNPOnC#$##C##%#G#s%JnC#$##Cs#'#%#G##(S#s%*RQMILNnC#$##C##%#G#s$vnC#$##C@#%#G##nK#$#'CN#+$#>)$#,&&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<-'#:#-#=#,-0C#s#Wj#.7#k#BS7Ck#CS7#US8IVOs'9s'5VOs'4s'1nC#$##C$#%#G##nC#$##Cs'@#%#E##nC#$##C<#%#G##nC#$##Cs#U#%#G##VNs&fs&bVNs&as&^nC#$##C$#%#G##nC#$##Cs&k#%#E##nC#$##C?#%#G##nC#$##Cs#Q#%#G##VLs'?s&8VLs&7s'BnC#$##C$#%#G##nC#$##Cs&?#%#E##nC#$##CB#%#G##nC#$##Cs#M#%#G##nK#$#$CO#+$#7s%0$#,/&#8#9#.)&#8#9#.)&#8#9#.)&#8#9#.)'#:#;#,#<#'#:#-#=#,#VS%s%os&jVS%s&ts%lnC#$##C$#%#G##nC#$##Cs%t#%#E##nC#$##Cs#%#%#G##nC#$##Cs#I#%#G##VPs%Gs%CVPs%Bs%?nC#$##C$#%#G##nC#$##Cs%L#%#E##nC#$##Cs#(#%#G##nC#$##Cs#E#%#G##nK#$#'CN#+$#>/$#,)&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<6'#:#-#=#,60C#s#|j#.s#%#k#<Ks(3US9I8S&URS#nF$D$#/C##%$#2s#|#EnF$D$#/C%#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(.$#/Cs(+#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s(0$#/Cs(/#%$#6##EnC#$##Cs#D#%#G#s%4nC#$##C$#%#G##US#S)US$S&nF$D$#/C##%$#2s#|#EnF$D$#/C%#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(8$#/Cs'Z#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s(:$#/Cs'^#%$#6##EnC#$##Cs#K#%#G#s%&nC#$##C$#%#G##US$S'US&S(nF$D$#/C##%$#2s#|#EnF$D$#/C%#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(B$#/Cs'1#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s(D$#/Cs'4#%$#6##EnC#$##Cs#R#%#G#s$tnC#$##C$#%#G##nK#$#$CO#+$#7s%`$#,7&#8#9#.-&#8#9#.-&#8#9#.-&#8#9#.-'#:#;#,#<#'#:#-#=#,#UMS$8RnF$D$#/C##%$#2s#|#EnF$D$#/C%#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(M$#/Cs&i#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s(O$#/Cs&l#%$#6##EnC#$##Cs#Y#%#G#s$fnC#$##C$#%#G##URS(US#S$nF$D$#/C##%$#2s#|#EnF$D$#/C%#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(W$#/Cs&E#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s(Y$#/Cs&I#%$#6##EnC#$##Cs#`#%#G#s$XnC#$##C$#%#G##nK#$#'CN#+$#>7$#,-&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<B'#:#-#=#,B0C#s$Xj#?s#9#UFs(_k#<K#US:IUOQULQnF$D$#/Cs%y#%$#2s$Y#EnF$D$#/Cs%{#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(g$#/C&#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s(i$#/C)#%$#6##EnC#$##C##%#G#s#;UNS#UMS#nF$D$#/Cs%j#%$#2s$X#EnF$D$#/Cs%l#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(p$#/C&#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s(r$#/C)#%$#6##EnC#$##C##%#G#s#:ULS$8S$nF$D$#/Cs%[#%$#2s$W#EnF$D$#/Cs%]#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s(y$#/C&#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s({$#/C)#%$#6##EnC#$##C##%#G#s#9nK#$#$CO#+$#7s&:$#,5&#8#9#.,&#8#9#.,&#8#9#.,&#8#9#.,'#:#;#,#<#'#:#-#=#,#US%MUNMnF$D$#/Cs%L#%$#2s$V#EnF$D$#/Cs%N#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s)'$#/C&#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s))$#/C)#%$#6##EnC#$##C##%#G#s#8UPRUIRnF$D$#/Cs%=#%$#2s$U#EnF$D$#/Cs%?#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s)0$#/C&#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s)2$#/C)#%$#6##EnC#$##C##%#G#s#7nK#$#'CN#+$#>5$#,,&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<?'#:#-#=#,?0C#s%0j#?s#4#nF$s)7$#/Cs&N#%$#3s#/#EnJ%DD$#6CH#$%#+#*#nF$s)9$#/Cs&Q#%$#6##E(ROQMILNPnC#$##C##%#G#s&>nC#$##C%#%#G##nF$s)=$#/Cs&<#%$#3s#,#EnJ%DD$#6CH#$%#+#*#nF$s)?$#/Cs&?#%$#6##E(S$NS#RQMILnC#$##C##%#G#s&,nC#$##C%#%#G##nF$s)C$#/Cs&*#%$#3s#)#EnJ%DD$#6CH#$%#+#*#nF$s)E$#/Cs&-#%$#6##E(S&LS$S#RQMInC#$##C##%#G#s%vnC#$##C%#%#G##nK#$#$CO#+$#7s&b$#,/&#8#9#.)&#8#9#.)&#8#9#.)&#8#9#.)'#:#;#,#<#'#:#-#=#,#nF$s)J$#/Cs%t#%$#3s#&#EnJ%DD$#6CH#$%#+#*#nF$s)L$#/Cs%w#%$#6##E(QS%MILNPOnC#$##C##%#G#s%dnC#$##C%#%#G##nF$s)P$#/Cs%b#%$#3s###EnJ%DD$#6CH#$%#+#*#nF$s)R$#/Cs%e#%$#6##E(S#PRQMILNnC#$##C##%#G#s%RnC#$##C%#%#G##nK#$#'CN#+$#>/$#,)&#8#9#.#&#8#9#.#&#8#9#.#&#8#9#.#'#:#;#,#<6'#:#-#=#,60C#s%Rj#Ds)|#[S1QMIs)\NPs)[nK#$#$CS%#+$#7#$#,s%n&#8#9#.s%V&#8#9#.s%V&#8#9#.s%V&#8#9#.s%V'#:#;#,#<s&C'#:#-#=#,s&C)MI)S#I*S(S#*S)Q#LS(##S%#PS#%$##OS###H#IS(%$#5'#+S'S)S(S&ILS%#NS$%H#nF$D$#/C%#%$#0##E+S'S$S#RPOH#MS)%H#nF$D$#/C%#%$#1##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#/C6#%$#2##EnF$D$#/C8#%$#)##EnJ%DD$#3CH#$%#4#5#nF$s)u$#/C;#%$#3##EnJ%DD$#6CH#$%#+#*#nF$s)w$#/C>#%$#6##E(MMILNPOS%3IP4#'KDPO$s)W#s)U,M#s'A'KDS%S-$s)Z#s)X$s)['#,Ms'N#nC#$##C'#%#G##nC#$##C+#%#E##nC#$##C.#%#G##nC#$##C0#%#G##nK#$#'CP#+$#>s#.$#,#&#8#9#.s'+&#8#9#.s'+&#8#9#.s'+&#8#9#.s'+'#:#;#,#<s&&'#:#-#=#,s&&VSBC#&I2#USCI1s*SIs#5&$#US;&USDI1s$0s$/s#Z%$#US<)USEI1s$ls$ks$5%$#US=,USFI1s%7s%6s$p%$#US4/USGI1s%Qs%Ps%<%$#US>2USHI1s&5s&4s%Z%$#USI5USJI1s*Gs*Fs&:%$#[S.8LNPOS%H[S/ILNPOS%H0C$#m#&#j#EK#6KCs*Us*T#j#FD#6Ds*ls*Zs*Y#j#GK#6Ks*ms*_s*^#j#HK#6Ks*ns*ds*c#j#ID#6Ds*os*is*h#j#/K#6Ks*ps*ns*m#j#Js*v##"). Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Lemma disj_sidesB_eqf : forall fk, disj_sidesB (mkbc fk) = disj_sides fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sidesB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.disj_sides); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itvB); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itvB_eqf)|] [|@n1; @k1; @b1; @kn; @k; @a; @w; @v; @n; @k0; @lo; @hi; @e; @m; @c1; @m1; @c2; @m2; @c; @l; @b; @IH; @rest; @K; @fk|] "#$8#3#G#%###$#&#:#)#(#9#'#7#*#H#=#?#-#<#2#+#,#E#1#6#B#G#I#D#;#C#0#/#J#@#>#F#A#8*#0(#C$#D&#E&#/(#;)#F(US(LVS-RJUS(#k#$G#k#%G#k#&J#$DUO#UPD$EVO#DVPED$CWO#EDWPCED$FXO#CEDXPFCED$S$'#FCED#S$FCED&5$#k#$G#k#%G#k#&J#j#';#US.L#M#CEDVS)<#j#$G#j#%G#j#&J#$S%'#FCED#S%FCED&s##$#k#$G#k#%G#k#&J##QKCED$S#ZS&#MHIFCXS*RJEDZS&%MHIEDXS*RJFC%s#.#KnN#$##s#.%#%###K%s#0'#nN#$##s#0)#%###$nL#$#(s#1H#-&#)#*#+F%#)#,C&#)#,#-F%#.#/C%#0#1C&#0#.#/F%#)#,C'#2#3#4#5#&#)#,#6F%#)#,C#S'S$HIK#S/MIKF(S#MHIFC(S#MHIED#S#S%MHI%s#8-#nN#$##s#8%#%###$%s#:1#nN#$##s#:(#%###$nL#$#(s#;H#-&#)#*#++%#)#,*&#)#,#-+%#.#/*%#0#1*&#0#.#/+%#)#,*'#2#3#4#5#&#)#,#6+%#)#,*&s#<-#j#7s#=#k#1JNk#6R#k#,G#k#(G#k#8J#US+QYKMHIFCYKMHIEDnN#$##s#F##%#1#2%s#H?#nN#$##s#H&#%###$nL#$#(s#IH#-&#)#*#+9%#)#,8&#)#,#-9%#.#/8%#0#18&#0#.#/9%#)#,8'#2#3#4#5#&#)#,#69%#)#,8&s#J#1j#8+##S0HKFC(S'HIKFC(S'HIKED%s#Ps#%?nN#$##s#P$#%###@%s#Rs#)#nN#$##s#R'#%###$nL#$#(s#SI#-&#)#*#+B%#)#,)&#)#,#-B%#.#/)%#0#1)&#0#.#/B%#)#,)'#2#3#4#5#&#)#,#6B%#)#,)VS)s#T#$QUS&#US1QZS,87/&$#'&KCEDWFCEDZS,s#[s#6@%$#%LIK'*#CED#Q$CED&s#_$#m#'#j#$G#j#%G#j#&J#j#9s#@#j#:s#g#j#;L#\S2Ls#Ps#J#FCEDj#$G#)Gs#is#[s#Z#j#%G#)Gs#js#`s#_#j#&J#)Js#ks#es#d#j#'s#p#)s#qs#ls#js#i#j#<s#r##"). Qed.
#[export] Hint Rewrite disj_sidesB_eqf : bceq.
Lemma disj_sides_xB_eqf : forall fk, disj_sides_xB (mkbc fk) = disj_sides_x fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sides_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.disj_sides_x); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itv_xB); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv_x); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itv_xB_eqf)|] [|@n1; @k1; @b1; @kn; @k; @a; @w; @v; @n; @k0; @lo; @hi; @e; @m; @c1; @m1; @c2; @m2; @c; @l; @b; @IH; @rest; @K; @fk|] "#$8#3#G#%###$#9#&#)#(#'#7#*#H#:#=#?#-#<#2#+#,#E#1#6#B#G#I#D#;#C#0#/#J#@#>#F#A#8*#0(#C$#D&#E&#/(#;)#F(US(KVS-RFUS(#k#$F#k#%N#k#&F#$DUO#UPD$EVO#DVPED$CWO#EDWPCED$GXO#CEDXPGCED$S$'#GCED#S$GCED&5$#k#$F#k#%N#k#&F#j#';#US.K#L#CEDVS)<#j#$F#j#%N#j#&F#$S%'#GCED#S%GCED&s##$#k#$F#k#%N#k#&F##QJCED$S#ZS&#LHIGCXS*RFEDZS&%LHIEDXS*RFGC%s#.#JnM#$##s#.%#%###J%s#0'#nM#$##s#0)#%###$nK#$#(s#1H#-&#)#*#+G%#)#,C&#)#,#-G%#.#/C%#0#1C&#0#.#/G%#)#,C'#2#3#4#5#&#)#,#6G%#)#,C#S'S$HIJ#S/LIJG(S#LHIGC(S#LHIED#S#S%LHI%s#8-#nM#$##s#8%#%###$%s#:1#nM#$##s#:(#%###$nK#$#(s#;H#-&#)#*#++%#)#,*&#)#,#-+%#.#/*%#0#1*&#0#.#/+%#)#,*'#2#3#4#5#&#)#,#6+%#)#,*&s#<-#j#7s#=#k#1FMk#6R#k#,F#k#(N#k#8F#US+QYJLHIGCYJLHIEDnM#$##s#F##%#1#2%s#H?#nM#$##s#H&#%###$nK#$#(s#IH#-&#)#*#+9%#)#,8&#)#,#-9%#.#/8%#0#18&#0#.#/9%#)#,8'#2#3#4#5#&#)#,#69%#)#,8&s#J#1j#8+##S0HJGC(S'HIJGC(S'HIJED%s#Ps#%?nM#$##s#P$#%###@%s#Rs#)#nM#$##s#R'#%###$nK#$#(s#SI#-&#)#*#+B%#)#,)&#)#,#-B%#.#/)%#0#1)&#0#.#/B%#)#,)'#2#3#4#5#&#)#,#6B%#)#,)VS)s#T#$QUS&#US1QZS,87/&$#'&JCEDWGCEDZS,s#[s#6@%$#%KIJ'*#CED#Q$CED&s#_$#m#'#j#$F#j#%N#j#&F#j#9s#@#j#:s#g#j#;K#\S2Ks#Ps#J#GCEDj#$F#)Fs#is#[s#Z#j#%N#)Ns#js#`s#_#j#&F#)Fs#ks#es#d#j#'s#p#)s#qs#ls#js#i#j#<s#r##"). Qed.
#[export] Hint Rewrite disj_sides_xB_eqf : bceq.
Lemma in_sidesB_eqf : forall fk, in_sidesB (mkbc fk) = in_sides fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sidesB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.in_sides); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itvB); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itvB_eqf); constr:(@Corelib.Init.Datatypes.pair); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr))|] [|@n2; @k2; @b2; @D; @l; @p; @b; @m; @c; @n; @k; @IH; @rest; @e; @s; @a; @fk|] "#$9#3#H###$#%#=#<#;#&#:#1#>#@#)#*#(#'#I#2#J#6#+#C#-#.#F#0#H#G#7#9#D#K#L#E#A#?#B#8(#E$#-(#F&#,(#G(US%S.VS/JHUS%#k#$GFk#%G#k#&H##CUL#UMC#DVL#CVMDC#EWL#DCWMEDC#IXL#EDCXMIEDC#S&&#IEDC$S&IEDC%F$#k#$G#k#%G#k#&H#j#'9#US0;$O#EDCVS'F#j#$G#j#%G#j#&H##S(&#IEDC$S(IEDC%F$#k#$G#k#%G#k#&H##S)WS*s#)PQ&$#EDC$S)$EDC%F$#k#$G#k#%G#k#&H#k##+#k#(s#0#j#)s#2##S+&#IEDC$S+IEDC%F$#k#$G#k#%G#k#&H#$KQEDC#S#ZS,#IEDONnF#$##F##%#R#CZS$S#IEDON$S#PIEDnF#$##F$#%#R##%F&#j#*F#k#+HFk#,J#k#-G#k#.G#k#*H#US$KYCIEDONnF#$##F##%#R#-%F#-j#*'#ZS$KEDCNPnF#$##F##%#R#6VS'F##KUS,#US1KZS-.-)&$#&&QEDCWIEDCZS-F>6%$#XS2JHNPWS*s#X#Q&+#EDC$K$EDC%F$#m#(#j#$G#j#%G#j#&H#j#/s#)#j#0s#`#j#+H#j#,J#V#DCj#1H#j#2J#YS3JHs#7#Cj#3s#h#\S4s#is#Qs#K#IEDCj#$G#'GFs#\s#[#j#%G#'Gs#ks#as#`#j#&H#'Hs#ls#fs#e#j#'s#o#'s#ps#ms#ks#j#j#4s#s##"). Qed.
#[export] Hint Rewrite in_sidesB_eqf : bceq.
Lemma in_sides_xB_eqf : forall fk, in_sides_xB (mkbc fk) = in_sides_x fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sides_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.in_sides_x); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itv_xB); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sub_itv_x); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sub_itv_xB_eqf); constr:(@Corelib.Init.Datatypes.pair)|] [|@n2; @k2; @b2; @D; @l; @p; @b; @m; @c; @n; @k; @IH; @rest; @e; @s; @a; @fk|] "#$9#3#H###$#;#%#=#&#<#:#1#>#@#)#*#(#'#I#2#J#6#+#C#-#.#F#0#H#G#7#9#D#K#L#E#A#?#B#8(#E$#-(#F&#,(#G(US%S.VS/JEUS%#k#$EGk#%I#k#&E##CUL#UMC#DVL#CVMDC#FWL#DCWMFDC#HXL#FDCXMHFDC#S&&#HFDC$S&HFDC%G$#k#$E#k#%I#k#&E#j#'9#US0;$O#FDCVS'G#j#$E#j#%I#j#&E##S(&#HFDC$S(HFDC%G$#k#$E#k#%I#k#&E##S)WS*s#)PQ&$#FDC$S)$FDC%G$#k#$E#k#%I#k#&E#k##+#k#(s#0#j#)s#2##S+&#HFDC$S+HFDC%G$#k#$E#k#%I#k#&E#$KQFDC#S#ZS,#HFDONnG#$##G##%#R#CZS$S#HFDON$S#PHFDnG#$##G$#%#R##%G&#j#*G#k#+EGk#,J#k#-E#k#.I#k#*E#US$KYCHFDONnG#$##G##%#R#-%G#-j#*'#ZS$KFDCNPnG#$##G##%#R#6VS'G##KUS,#US1KZS-.-)&$#&&QFDCWHFDCZS-G>6%$#XS2JENPWS*s#X#Q&+#FDC$K$FDC%G$#m#(#j#$E#j#%I#j#&E#j#/s#)#j#0s#`#j#+E#j#,J#V#DCj#1E#j#2J#YS3JEs#7#Cj#3s#h#\S4s#is#Qs#K#HFDCj#$E#'EGs#\s#[#j#%I#'Is#ks#as#`#j#&E#'Es#ls#fs#e#j#'s#o#'s#ps#ms#ks#j#j#4s#s##"). Qed.
#[export] Hint Rewrite in_sides_xB_eqf : bceq.
Scheme kc__3 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr Sort Prop.
Lemma mk_sprepB_eqf : forall fk, mk_sprepB (mkbc fk) = mk_sprep fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mk_sprep); constr:(@kc__3); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SPrep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sdmemo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sidesM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.unit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sides_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.disj_sides); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.disj_sides_x); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sidesB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sidesB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sides_xB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.disj_sidesM_eq); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EVar); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EAlu); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EAluw); constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EMd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EMdw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EExt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EBlob)|] [|@n1; @k1; @z1; @n; @op; @a; @b; @sx; @lo; @e; @k; @i; @l; @b1; @kn; @o; @z; @x1_2; @x1_1; @x1; @x0; @x; @fk|] "#(6#1#c#9#K#.#(#,#$###-#7#%#&#'#)#/#8#\#*#0#J#+#:#<#^#a#L#R#4#H#I#O#T#P#N#A#M#@#5#C#F#D#E#Y#[#=#?#>#Q#;#U#G#B#S#V#W#X#Z#]#_#`#b#c#d#e#6E#O'#P&#Q)#B(#C%#R$#)$#D%#('#S%#E%#T$#F%#@(#U%#V$#B$#C$#E$#W$#F$#X$#D$#Y$#;$#Z$#[$#\&#]&#^&#_&#`'#a'#b(US-S7k#$KCk#%Q#(IUS'#US(I(HVS'#IVS(HI(LWS'#HIWS(LHI(N/#M*$I1S8KUS-#(F.#US.I1'S%US/#ZS9'&NM%#WS:)S;#US/+nK#$#$+I#+$#&$$#'#&#(#)#*#&#(#)#*#&#(#)#*#&#(#)#*#'#+#,#'#-#'#+#.#/#'#YS++*NMHj##D##10%#-NM'NI0FFNM.nK#$#$2I#+$#&#$#'*&#(#)#**&#(#)#**&#(#)#**&#(#)#**'#+#,#'#-*'#+#.#/#'*&FFNMHj##D##('%#$C*#j#-K#YS,76NM5(O/#F2H*%#(S#.#2LYS+%$OF#j##D##*(I#-OF'O+US.H0OOFN#&S#S#OF*j##D##('%#$C*#j#0s#+#k#$Ks#,k#%Q#k#1K#k#2s#?#3F.:YS,;#FN/+7OF6j##D##=;%#$C#/j#0*#k#$Qs#8k#%Q#k#1K#k#2s#K#US0FXI.FN:&S#BOFAj##D##s#(s#&%#$C#:j#0)#US1Qk#-K#4F)s#-0O8FNs#$#s#0$#+$C#Bj#3(#1QQUS1#k#-K#5F)F##s#.+3$C#s#*j#3'#0OIFNs#0&S#HOFs#7j##D##s#5s#4%#$C#s#0j#0s#h#-FN2I'F#&OOFNs#Cj##D##'%s#O#,C#6F%s#qF+$s#_#7s#a8F%984%$#9s#d:F%s#%s#$?%$#US,s#gUS<F%s#1s#0s#*%$#;s#j<F%s#@s#?s#8%$#YS=s#ms#lNMs#k%s#os#Ys#F$s#h#j#4Q#U#Ij#4Q#=H*s#]#=L+s#ZOF#j##D##s#`&s#p#'O(&S#S#OF'j##D##s#[%s#t#$C'#j#0s#Q#).&S#s#dOF-j##D##s#j%s#z#$C#)j#3s#B##s#8.s#}&$C#,j#3s#<#&S#HOF5j##D##s#i3s$&#$C#1j#0s$@#=I'F#&OOFN>j##D##s#:%s$-#,C#%s$GF)#s$5s#5%s#Is#H/#s#4s#3%s#Ss#R3#s#2s#1%s#is#h:#s#-s#,j#'R#U#Ij#'R#3G(J/#G>MLH*%#(E.#>NML+$JG#j##D##*(s$@#-JG'J+&EEJG(j##D##&%s$E#$C(#j#0s#~#4G)2&E0JG/j##D##6%s$L#$C#*j#3s#p#5G)G##1s$Q($C#/j#3s#l#&EHJG9j##D##76s$V#$C#4j#0s$p#-GS&>LHI'G#&JJGS&s#%j##D##'%s$^#,C#(G.#6G%s${G-&$#7&8G%s$#95%$#9):G%s$/s##=%$#;,<G%s$Gs#8s#'%$#j#5K#j#6K#j#(S)#W#LHIj#*K#j#)K#j#(S)#?MLH*s#@#?NML+s#=JG#j##D##s#C&s$y#'J(&EEJG'j##D##s#>%s$}#$C'#j#0s$Z#).&Es#GJG-j##D##s#M%s%'#$C#)j#3s$K##s#8.s%*&$C#,j#3s$E#&EHJG5j##D##s#L3s%/#$C#1j#0s%I#?LHI'G#&JJGS&>j##D##s#;%s%6#,C#%s%PG)#s#5s#4%s$Rs#H/#s#3s#2%s$\s#P3#s#1s#0%s$rs#c:#s#/s#.j#5K#j#6K#j#(S)#W#LHIj#*K#j#)K#j#(S)#@MLH*s#k#@NML+s#hJG#j##D##s#n&s%H#'J(&EEJG'j##D##s#i%s%L#$C'#j#0s%)#).&Es#rJG-j##D##s#x%s%R#$C#)j#3s$v##s#c.s%U&$C#,j#3s$p#&EHJG5j##D##s#w3s%Z#$C#1j#0s%t#@LHI'G#&JJGS&>j##D##s#f%s%a#,C#%s%{G)#s#`s#_%s$}s#s/#s#^s#]%s%+s#{3#s#\s#[%s%As$2:#s#Zs#Yj#5K#j#6K#j#(S*#W#LHIj#*K#j#)K#j#(S*#AMLH*s$:#ANML+s$7JG#j##D##s$=&s%s#'J(&EEJG'j##D##s$8%s%w#$C'#j#0s%T#).&Es$AJG-j##D##s$G%s%}#$C#)j#3s%E##s$2.s&$&$C#,j#3s%?#&EHJG5j##D##s$F3s&)#$C#1j#0s&C#ALHI'G#&JJGS&>j##D##s$5%s&0#,C#%s&JG)#s$/s$.%s%Ls$B/#s$-s$,%s%Vs$J3#s$+s$*%s%ls$]:#s$)s$(j#5K#j#6K#j#(S*#W#LHIj#*K#j#)K#j#(S*#3E(P/#EBNMLH*%#(S$.#BFNML+$PE#j##D##*(s&G#-PE'P+&S$S$PE(j##D##&%s&L#$C(#j#0s&)#4E)2&S$0PE/j##D##6%s&S#$C#*j#3s%w#5E)E##1s&X($C#/j#3s%s#&S$HPE9j##D##76s&]#$C#4j#0s&w#-EJBMLHI'E#&PPEJs#%j##D##'%s&e#,C#6E%s'$E+$s%.#7s%08E%s&(73%$#9s%3:E%s&4A;%$#;s%6<E%s&Ls#6s#%%$#j#7K#j#'R#j#,R#j#+S%#X#MLHIj#-K#j#'R#j#,R#j#+S%#CNMLH*s#@#CFNML+s#=PE#j##D##s#C&s'$#'P(&S$S$PE'j##D##s#>%s'(#$C'#j#0s&a#).&S$s#GPE-j##D##s#M%s'.#$C#)j#3s&R##s#8.s'1&$C#,j#3s&L#&S$HPE5j##D##s#L3s'6#$C#1j#0s'P#CMLHI'E#&PPEJ>j##D##s#;%s'=#,C#%s'WE)#s%as#6%s&Ys#H/#s#5s#4%s&cs#P3#s#3s#2%s&ys#c:#s#1s#0j#'R#j#/Q#j#.R#j#+S%#X#MLHIj#'R#j#/Q#j#.R#j#+S%#^S>s'?s&@s%us%7s$hs$=s#ns#0#I(MXS'#LHIXS(MLHI$C$#m#'#j#7K#DKCs'as'`#j#8Q#DQs'ls'fs'e#j#9K#DKs'ms'ks'j#j#:s'p##"). Qed.
#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Lemma ranges_apart_pB_eqf : forall fk, ranges_apart_pB (mkbc fk) = ranges_apart_p fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_p); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.in_sides_x); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_rng); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sidesB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_D); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apartB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_h1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.end_hiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_Dx); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.shares_var); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.in_sides); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_apart); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.end_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apartB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.end_hiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sidesB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sides_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sides_xB_eqf)|] [|@n2; @k2; @b2; @n1; @k1; @b1; @D; @p0; @lo2; @hi2; @x; @p; @lo1; @hi1; @e1; @e2; @h2; @h1; @z2; @n; @op; @a; @b; @sx; @lo; @e; @k; @i; @z1; @o; @neg; @pos; @x5; @x4; @x3; @x2; @x1; @x0; @fk|] "#,(#9#p#B#A#Q#R#P###G#@#%#(#&#$#'#*#)#0#-#.#/#,#2#1#+#3#4#5#a#C#E#6#Z#7#8#d#e#<#I#T#S#U#g#i#h#f#b#L#W#]#X#?#=#H#`#j#k#l#m#n#o#p#q#r#N#M#^#D#_#c#J#F#>#K#V#Y#\#[#O<#a%#b%#c&#d$#e'#K*#M&#S*#R&#f%#g&#h)#i(#j$#k$#l%#m%#n$#O%#N%#G(#P%#Q%#o$#)%US6SEk#$JCk#%D#k#&J#k#'J#k#(D#k#)J#&HUS.#US/H&NVS.#HVS/NH&KWS.#NHWS/KNH&MXS.#KNHXS/MKNH&OYS.#MKNHYS/OMKNH&LZS.#OMKNHZS/LOMKNH&Q[S.#LOMKNH[S/QLOMKNH;SFJUS6#k#*#=US7P;DD0S&&R8#S)#MR:P#$##NS#$$##HS#:Q#$##OR$$#nC#$##C(#%#G##nI%DD$#+CH#$%#,#-#nF$2$#.C/#%$#+##EnI%DD$#/CH#$%#0#1#nF$4$#.C3#%$#/##E&S#US8S&:HYS9%$LO#:N[S:'S)P#LO%nC#$##C%#%#G##nC#$##C*#%#G##1S'&S+9#S##LS'##N#MS%$$##KS%##H#QS'$$#nC#$##C'#%#G##&S,*#S*S'S(QLN$H?nF$D$#.C$#%$#2##E*&RS%S$MKH#PS*$H#nF$D$#.C%#%$#3##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#.C6#%$#4##EnF$D$#.C9#%$#5##EnI%DD$#+CH#$%#,#-#nF$s#6$#.Cs#3#%$#+##EnI%DD$#/CH#$%#0#1#nF$s#8$#.Cs#7#%$#/##E2S&S1XK#LOM3S)L4#;JD'JDLOUSG$%%$#'JDS)P'JDQS-%(#&%)%#+s#2'#%+')'JDMS-%-#+%.-#+s#7&#nC#$##C(#%#G##nC#$##C2#%#E##nC#$##C5#%#G##nC#$##C8#%#G##0S$&S'8#S#1S+&S09#S%#LS+##N#MS($$##KS(##H#QS+$$#nC#$##C'#%#G##&S2*#S,S+S*QLN#OS'$H#nF$D$#.C%#%$#2##E*'S'S(RMKH#PS,$H#nF$D$#.C%#%$#3##EnC#$##C'#%#G##nC#$##C-#%#G##nF$D$#.C7#%$#4##EnF$D$#.C:#%$#5##EnI%DD$#+CH#$%#,#-#nF$s#l$#.C=#%$#+##EnI%DD$#/CH#$%#0#1#nF$s#n$#.CA#%$#/##E2S$S1XO#PQL3S#P4#&S%'JDPQ%s#:#s#8'JDS#S&'JDS)S-%s#=#s#;%s#>%#+)'#%s#@'s#>'JDLS-%s#B#s#@%s#C,#+.&#nC#$##C(#%#G##nC#$##C1#%#E##nC#$##C4#%#G##nC#$##C7#%#G##0S%&S*8#S$1S,9s#,R#LS,##N#MS'$$##KS'##H#QS,$$#nC#$##C'#%#G##&S3*#S0S,S+QLN#OS*$H#nF$D$#.C%#%$#2##E*'S*S'S(MKH#PS0$H#nF$D$#.C%#%$#3##EnC#$##C'#%#G##nC#$##C-#%#G##nF$D$#.C7#%$#4##EnF$D$#.C9#%$#5##EnI%DD$#+CH#$%#,#-#nF$s$D$#.C<#%$#+##EnI%DD$#/CH#$%#0#1#nF$s$F$#.C@#%$#/##E2S%S1XL#S)PQ3S$S)4#'JDS$S#'JDS&S-%s#n#s#l%s#o%#+s$Ms#g#%s#q's#o+s$O#s#knC#$##C%#%#G##nC#$##C+#%#E##nC#$##C.#%#G##nC#$##C1#%#G##nJ#$#$CK#+$#6s$<$#7s#f&#8#9#:s#1&#8#9#:s#1&#8#9#:s#1&#8#9#:s#1'#;#<#7#=#'#;#>#?#7#0S)8s#CP1S(9s#3S&#LS(##N#MS$$$##KS$##H#QS($$#nC#$##C'#%#G##*s$HS'S(RQLN#OS%$H#nF$D$#.C%#%$#2##E*s$LS%S$S#MKH#PS'$H#nF$D$#.C%#%$#3##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#.C6#%$#4##EnF$D$#.C8#%$#5##EnI%DD$#+CH#$%#,#-#nF$s$q$#.C;#%$#+##EnI%DD$#/CH#$%#0#1#nF$s$s$#.C>#%$#/##E2S)S1XN#OMK3PO4#&S&'JDOM%s$?#s$=+%#s#['JDKS-%s$B#s$@%s$C'#+)s#h#nC#$##C'#%#G##nC#$##C,#%#E##nC#$##C/#%#G##nC#$##C2#%#G##0S#&S(8#S&1S*9s$aS$#LS*##N$#s%+#KR##H#QS*$$#nC#$##C'#%#G##*s$@S+S*S'QLN#OS($H#nF$D$#.C%#%$#2##E*s$DS(RS%MKH#PS+$H#nF$D$#.C%#%$#3##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#.C5#%$#4##EnF$D$#.C7#%$#5##EnI%DD$#+CH#$%#,#-#nF$s%B$#.C:#%$#+##EnI%DD$#/CH#$%#0#1#nF$s%D$#.C>#%$#/##E2S#S1XM#QLO3S&Q4#&S$'JDQL%s$l#s$j'JDS&S)'JDPS-%s$o#s$m%s$p%#+)'#%s$r's$p'JDOS-%s$t#s$r%s$u,#+.&#nC#$##C(#%#G##nC#$##C1#%#E##nC#$##C4#%#G##nC#$##C7#%#G##nJ#$#'CO#+$#@s#b$#7s#5&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=s$5'#;#>#?#7s$55RS),s%Ts%OnI%DD$#+CH#$%#,#-#nF$s%^$#.C%#%$#+##EnI%DD$#/CH#$%#0#1#nF$s%`$#.Cs%_#%$#/##EYS4S#s%MLOs%L[S5S#S)Ps%KLOs%MnC#$##C$#%#G##nC#$##C&#%#G##6S+S#,s%Es%A(S,S*S'S(QLNnF$D$#.C##%$#2s%?#E(S,RS%S$MKHnF$D$#.C##%$#3s%=#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#.C*#%$#4##EnF$D$#.Cs%S#%$#5##EnI%DD$#+CH#$%#,#-#nF$s%p$#.C7#%$#+##EnI%DD$#/CH#$%#0#1#nF$s%r$#.Cs%q#%$#/##E7S#s%<LOM)S#s%6s%2)S#s%1s%.nC#$##C$#%#G##nC#$##Cs%=#%#E##nC#$##C'#%#G##nC#$##C)#%#G##5S'S#6S0S%,s%&s$~(S2S,S+S*QLNnF$D$#.C##%$#2s${#E(S2S'S(RMKHnF$D$#.C##%$#3s$y#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#.C*#%$#4##EnF$D$#.Cs%4#%$#5##EnI%DD$#+CH#$%#,#-#nF$s&*$#.C.#%$#+##EnI%DD$#/CH#$%#0#1#nF$s&,$#.Cs%;#%$#/##E7S%s$xPQL)S%s$ss$o)S%s$ns$knC#$##C$#%#G##nC#$##Cs$y#%#E##nC#$##C'#%#G##nC#$##C)#%#G##5S*S$6S2R,s$ds$`(S3S0S,S+QLNnF$D$#.C##%$#2s$]#E(S3S*S'S(MKHnF$D$#.C##%$#3s$[#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#.C*#%$#4##EnF$D$#.Cs$q#%$#5##EnI%DD$#+CH#$%#,#-#nF$s&@$#.C.#%$#+##EnI%DD$#/CH#$%#0#1#nF$s&B$#.Cs$x#%$#/##E7Rs$ZS)PQ)Rs%\s$T)Rs$Ss%_nC#$##C$#%#G##nC#$##Cs$[#%#E##nC#$##C'#%#G##nC#$##C)#%#G##nJ#$#$CK#+$#6s#D$#7s#/&#8#9#:9&#8#9#:9&#8#9#:9&#8#9#:9'#;#<#7#=#'#;#>#?#7#5S%P6S*S&,s$Ms$I(S+S'S(RQLNnF$D$#.C##%$#2s$G#E(S+S%S$S#MKHnF$D$#.C##%$#3s$E#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#.C*#%$#4##EnF$D$#.Cs$Z#%$#5##EnI%DD$#+CH#$%#,#-#nF$s&W$#.C.#%$#+##EnI%DD$#/CH#$%#0#1#nF$s&Y$#.Cs$`#%$#/##E7S&s$DOMK)S&s$?s%;)S&s%Es$<nC#$##C$#%#G##nC#$##Cs$E#%#E##nC#$##C'#%#G##nC#$##C)#%#G##5S(S&6S,S$,s$6s$2(S0S+S*S'QLNnF$D$#.C##%$#2s$0#E(S0S(RS%MKHnF$D$#.C##%$#3s$.#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#.C*#%$#4##EnF$D$#.Cs$B#%$#5##EnI%DD$#+CH#$%#,#-#nF$s&m$#.C.#%$#+##EnI%DD$#/CH#$%#0#1#nF$s&o$#.Cs$I#%$#/##E7S$s$-QLO)S$s$(s$$)S$s$#s#|nC#$##C$#%#G##nC#$##Cs$.#%#E##nC#$##C'#%#G##nC#$##C)#%#G##nJ#$#'CO#+$#@s#/$#79&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=s#F'#;#>#?#7s#F-Cs#|#j#:s&{#k#$DCk#%D#k#&J#k#*s'$#US4PXKs&kLOs&jnC#$##C##%#G#s&hnC#$##Cs&o#%#G##nC#$##Cs#m#%#G#s&8nC#$##Cs&M#%#G##nC#$##Cs#Y#%#G#s%anC#$##Cs%u#%#G##nC#$##Cs#E#%#G#s%5nC#$##Cs%C#%#G##nJ#$#$CK#+$#6)$#7'&#8#9#:%&#8#9#:%&#8#9#:%&#8#9#:%'#;#<#7#=#'#;#>#?#7#nC#$##Cs#1#%#G#s$fnC#$##Cs$u#%#G##nC#$##C=#%#G#s$6nC#$##Cs$J#%#G##nJ#$#'CO#+$#@'$#7%&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=*'#;#>#?#7*-C#9j#:4#UFDk#5D#k#1D#k#0D#k#7J#k#>D#k#:J#US;PnC#$##Cs$9#%#G#s'$nC#$##Cs'+#%#G##ZS#S*S'S(QLNnF$D$#.C##%$#2s&r#EZS#RS%S$MKHnF$D$#.C##%$#3s&p#EnC#$##C%#%#G##nC#$##Cs&y#%#G##nF$D$#.Cs''#%$#4##EnF$D$#.Cs'*#%$#5##EnI%DD$#+CH#$%#,#-#nF$s'G$#.Cs'D#%$#+##EnI%DD$#/CH#$%#0#1#nF$s'I$#.Cs'H#%$#/##EnC#$##C##%#G#s#&ZS%S,S+S*QLNnF$D$#.C##%$#2s&I#EZS%S'S(RMKHnF$D$#.C##%$#3s&G#EnC#$##C%#%#G##nC#$##Cs&Q#%#G##nF$D$#.Cs&[#%$#4##EnF$D$#.Cs&^#%$#5##EnI%DD$#+CH#$%#,#-#nF$s'T$#.Cs&a#%$#+##EnI%DD$#/CH#$%#0#1#nF$s'V$#.Cs&e#%$#/##EnC#$##C##%#G#s#1ZRS0S,S+QLNnF$D$#.C##%$#2s%~#EZRS*S'S(MKHnF$D$#.C##%$#3s%|#EnC#$##C%#%#G##nC#$##Cs&*#%#G##nF$D$#.Cs&4#%$#4##EnF$D$#.Cs&6#%$#5##EnI%DD$#+CH#$%#,#-#nF$s'a$#.Cs&9#%$#+##EnI%DD$#/CH#$%#0#1#nF$s'c$#.Cs&=#%$#/##EnC#$##C##%#G#s#<nJ#$#$CK#+$#6s#*$#7=&#8#9#:0&#8#9#:0&#8#9#:0&#8#9#:0'#;#<#7#=#'#;#>#?#7#ZS&S'S(RQLNnF$D$#.C##%$#2s%_#EZS&S%S$S#MKHnF$D$#.C##%$#3s%]#EnC#$##C%#%#G##nC#$##Cs%f#%#G##nF$D$#.Cs%p#%$#4##EnF$D$#.Cs%r#%$#5##EnI%DD$#+CH#$%#,#-#nF$s'o$#.Cs%u#%$#+##EnI%DD$#/CH#$%#0#1#nF$s'q$#.Cs%x#%$#/##EnC#$##C##%#G#s#GZS$S+S*S'QLNnF$D$#.C##%$#2s%?#EZS$S(RS%MKHnF$D$#.C##%$#3s%=#EnC#$##C%#%#G##nC#$##Cs%F#%#G##nF$D$#.Cs%O#%$#4##EnF$D$#.Cs%Q#%$#5##EnI%DD$#+CH#$%#,#-#nF$s'|$#.Cs%T#%$#+##EnI%DD$#/CH#$%#0#1#nF$s'~$#.Cs%X#%$#/##EnC#$##C##%#G#s#RnJ#$#'CO#+$#@=$#70&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=s#+'#;#>#?#7s#+-C#s#hj#As#J#k#BS<Ck#CS<#US=PnC#$##Cs'`#%#G#s$ynF$D$#.Cs'j#%$#4##EnF$D$#.Cs'm#%$#5##EnI%DD$#+CH#$%#,#-#nF$s(.$#.Cs(+#%$#+##EnI%DD$#/CH#$%#0#1#nF$s(0$#.Cs(/#%$#/##EVKs'Os'KVKs'Js'GnC#$##C$#%#G##nC#$##Cs'V#%#E##nC#$##Cs$|#%#G##nC#$##C(#%#G##nC#$##Cs'8#%#G#s$pnF$D$#.Cs'B#%$#4##EnF$D$#.Cs'E#%$#5##EnI%DD$#+CH#$%#,#-#nF$s(;$#.Cs'H#%$#+##EnI%DD$#/CH#$%#0#1#nF$s(=$#.Cs'L#%$#/##EVOs''s'#VOs&~s&{nC#$##C$#%#G##nC#$##Cs'-#%#E##nC#$##Cs$s#%#G##nC#$##C(#%#G##nC#$##Cs&m#%#G#s$gnF$D$#.Cs&w#%$#4##EnF$D$#.Cs&y#%$#5##EnI%DD$#+CH#$%#,#-#nF$s(H$#.Cs&|#%$#+##EnI%DD$#/CH#$%#0#1#nF$s(J$#.Cs'$#%$#/##EVLs'cs&[VLs&Zs'fnC#$##C$#%#G##nC#$##Cs&b#%#E##nC#$##Cs$j#%#G##nC#$##C(#%#G##nJ#$#$CK#+$#6s#r$#7=&#8#9#:0&#8#9#:0&#8#9#:0&#8#9#:0'#;#<#7#=#'#;#>#?#7#nC#$##Cs&M#%#G#s$^nF$D$#.Cs&W#%$#4##EnF$D$#.Cs&Y#%$#5##EnI%DD$#+CH#$%#,#-#nF$s(V$#.Cs&\#%$#+##EnI%DD$#/CH#$%#0#1#nF$s(X$#.Cs&_#%$#/##EVNs&=s'9VNs'Cs&:nC#$##C$#%#G##nC#$##Cs&C#%#E##nC#$##Cs$a#%#G##nC#$##C(#%#G##nC#$##Cs&-#%#G#s$UnF$D$#.Cs&6#%$#4##EnF$D$#.Cs&8#%$#5##EnI%DD$#+CH#$%#,#-#nF$s(c$#.Cs&;#%$#+##EnI%DD$#/CH#$%#0#1#nF$s(e$#.Cs&?#%$#/##EVMs%ys%uVMs%ts%qnC#$##C$#%#G##nC#$##Cs&##%#E##nC#$##Cs$X#%#G##nC#$##C(#%#G##nJ#$#'CO#+$#@=$#70&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=s#+'#;#>#?#7s#+-C#s$Tj#:s#H#k#=Js$=US>PUS&S#nF$D$#.C##%$#4s#J#EnF$D$#.Cs(X#%$#5##EnI%DD$#+CH#$%#,#-#nF$s(u$#.Cs(r#%$#+##EnI%DD$#/CH#$%#0#1#nF$s(w$#.Cs(v#%$#/##EnC#$##C##%#G#s%^US$S%nF$D$#.C##%$#4s#E#EnF$D$#.Cs(+#%$#5##EnI%DD$#+CH#$%#,#-#nF$s(}$#.Cs(.#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)#$#.Cs(2#%$#/##EnC#$##C##%#G#s%PUS%RnF$D$#.C##%$#4s#@#EnF$D$#.Cs'Z#%$#5##EnI%DD$#+CH#$%#,#-#nF$s))$#.Cs']#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)+$#.Cs'a#%$#/##EnC#$##C##%#G#s%BnJ#$#$CK#+$#6s$N$#73&#8#9#:+&#8#9#:+&#8#9#:+&#8#9#:+'#;#<#7#=#'#;#>#?#7#US)S&nF$D$#.C##%$#4s#;#EnF$D$#.Cs'5#%$#5##EnI%DD$#+CH#$%#,#-#nF$s)2$#.Cs'8#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)4$#.Cs';#%$#/##EnC#$##C##%#G#s%4US#S$nF$D$#.C##%$#4s#6#EnF$D$#.Cs&k#%$#5##EnI%DD$#+CH#$%#,#-#nF$s):$#.Cs&n#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)<$#.Cs&r#%$#/##EnC#$##C##%#G#s%&nJ#$#'CO#+$#@3$#7+&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=<'#;#>#?#7<-C#s%&j#As#/#k#'Ds%#k#(D#k#)J#US5PZKS)Ps).LOs)0nC#$##Cs&C#%#G##nC#$##Cs)5#%#G##nF$D$#.Cs&A#%$#4s#|#EnF$D$#.Cs).#%$#5##EnI%DD$#+CH#$%#,#-#nF$s)K$#.Cs)H#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)M$#.Cs)L#%$#/##EnC#$##C##%#G#s&4nF$D$#.Cs&2#%$#4s#v#EnF$D$#.Cs(\#%$#5##EnI%DD$#+CH#$%#,#-#nF$s)R$#.Cs(_#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)T$#.Cs(c#%$#/##EnC#$##C##%#G#s&%nF$D$#.Cs&##%$#4s#p#EnF$D$#.Cs(.#%$#5##EnI%DD$#+CH#$%#,#-#nF$s)Y$#.Cs(1#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)[$#.Cs(5#%$#/##EnC#$##C##%#G#s%rnJ#$#$CK#+$#68$#71&#8#9#:*&#8#9#:*&#8#9#:*&#8#9#:*'#;#<#7#=#'#;#>#?#7#nF$D$#.Cs%p#%$#4s#j#EnF$D$#.Cs'd#%$#5##EnI%DD$#+CH#$%#,#-#nF$s)a$#.Cs'g#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)c$#.Cs'j#%$#/##EnC#$##C##%#G#s%cnF$D$#.Cs%a#%$#4s#d#EnF$D$#.Cs'=#%$#5##EnI%DD$#+CH#$%#,#-#nF$s)h$#.Cs'@#%$#+##EnI%DD$#/CH#$%#0#1#nF$s)j$#.Cs'D#%$#/##EnC#$##C##%#G#s%TnJ#$#'CO#+$#@1$#7*&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=9'#;#>#?#79-C#s%Tj#:s#-#UFs)ok#=J#US?PULS)nF$s)s$#.C##%$#+s)d#EnI%DD$#/CH#$%#0#1#nF$s)u$#.Cs)t#%$#/##EnC#$##C##%#G#s&qnF$s)w$#.C'#%$#+s#/#EnI%DD$#/CH#$%#0#1#nF$s)y$#.Cs)x#%$#/##EnC#$##C##%#G#s&`UPS#nF$s)|$#.C##%$#+s#-#EnI%DD$#/CH#$%#0#1#nF$s)~$#.Cs)1#%$#/##EnC#$##C##%#G#s&OUS)S$nF$s*%$#.C##%$#+s#+#EnI%DD$#/CH#$%#0#1#nF$s*'$#.Cs(]#%$#/##EnC#$##C##%#G#s&>nJ#$#$CK#+$#61$#7-&#8#9#:(&#8#9#:(&#8#9#:(&#8#9#:('#;#<#7#=#'#;#>#?#7#UOPnF$s*+$#.C##%$#+s#)#EnI%DD$#/CH#$%#0#1#nF$s*-$#.Cs(4#%$#/##EnC#$##C##%#G#s&-UQS&nF$s*0$#.C##%$#+s#'#EnI%DD$#/CH#$%#0#1#nF$s*2$#.Cs'h#%$#/##EnC#$##C##%#G#s%xnJ#$#'CO#+$#@-$#7(&#8#9#:#&#8#9#:#&#8#9#:#&#8#9#:#'#;#<#7#=3'#;#>#?#73-C#s%xj#As#$##s)ss*2#NS&$$##HS&##s*1$#s(5,&#nI%DD$#+CH#$%#,#-#nF$s*?$#.Cs&R#%$#+##EnI%DD$#/CH#$%#0#1#nF$s*A$#.Cs(H#%$#/##EUS8S)YS4S&#OMs*.[S5S&PQs*-OMs*/nC#$##C$#%#G##nC#$##C'#%#G##nJ#$#$CN#+$#6#$#7s&E&#8#9#:s&/&#8#9#:s&/&#8#9#:s&/&#8#9#:s&/'#;#<#7#=s&r'#;#>#?#7s&r0P5S$Q1R6S'S)#LR##N#MS#$$##KS###H#QR$$#,'#(S*S(RS%QLN#OS$$H#nF$D$#.C%#%$#2##E(S*S$S#S&MKH#PS($H#nF$D$#.C%#%$#3##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#.C6#%$#4##EnF$D$#.C8#%$#5##EnI%DD$#+CH#$%#,#-#nF$s*b$#.C;#%$#+##EnI%DD$#/CH#$%#0#1#nF$s*d$#.C>#%$#/##E2PS17S)#MKN3QM4#'JDMK%s*/#s*-)S)#s'u'JDNS-%s*2#s*0%s*3'#)S)s(&#nC#$##C'#%#G##nC#$##C+#%#E##nC#$##C.#%#G##nC#$##C1#%#G##nJ#$#'CM#+$#@s#/$#7#&#8#9#:s'Y&#8#9#:s'Y&#8#9#:s'Y&#8#9#:s'Y'#;#<#7#=s&\'#;#>#?#7s&\VSHC#&PUS@#USIP.s#gs#fs#E&$#US:&USJP.s$;s$:s#l%$#USA)USKP.s$ns$ms$A%$#USB,USLP.s%\s%[s$r%$#USC/USMP.s&Ms&Ls%a%$#US92USNP.s&is&hs&W%$#USO5USPP.s+1s+0s&p%$#\S.8QLOMKNH\S/PQLOMKNH-C$#m#&#j#DJ#/JCs+;s+:#j#ED#/Ds+Vs+@s+?#j#FJ#/Js+Ws+Es+D#j#GJ#/Js+Xs+Js+I#j#HD#/Ds+Ys+Os+N#j#IJ#/Js+Zs+Ts+S#j#.SD#/SDs+[s+Ys+X#j#Js+b##"). Qed.
#[export] Hint Rewrite ranges_apart_pB_eqf : bceq.

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Fixpoint coeffs_divkB (bc : bctx) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0) && coeffs_divkB bc m rest)%lzb
  end.
Local Close Scope lzb_scope.

Definition lin_lowbits_knB (bc : bctx) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divkB bc (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
  else pageup_low e (2 ^ k).

Local Open Scope lzb_scope.
Definition lin_nowrap_lB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%lzb
  | None => false
  end.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrapB bc a)%lzb
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    match (if (negb (lin_trivial l) && lin_nowrapB bc a)%lzb then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_lB bc (fst l) rts then erangeB bc (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.
Local Close Scope lzb_scope.

Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some ((z mod two64) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
  end.

Local Open Scope lzb_scope.
Fixpoint lsplit_divB (bc : bctx) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divB bc m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0)%lzb then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.
Local Close Scope lzb_scope.

Definition and_high_splitB (bc : bctx) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.

Definition and_low_splitB (bc : bctx) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
      else mkAlu ALU_AND r bk
  | None => mkAlu ALU_AND r bk
  end.

Local Open Scope lzb_scope.
Definition narrow_maskB (bc : bctx) (a : expr) (k' : Z) : option Z :=
  let i := ctz64 k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%lzb then
    match xhiB bc a with
    | Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition mkAnd0B (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (k mod two64)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%lzb then
        (* [comment removed for export] *)
        (if Z.leb j (ealignB bc a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divkB bc (2 ^ j) (snd l))%lzb
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else (* [comment removed for export] *)
                match (if lin_trivial l then ([], snd l) else lsplit_divB bc (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
                | _ => (* [comment removed for export] *)
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrlB bc a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%lzb then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealignB bc a) then ELit 0
           else match lowbitsB bc a j2 with        (* [comment removed for export] *)
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_knB bc a j2 with
                | Some v => ELit v
                | None => (* [comment removed for export] *)
                    match lsplit_divB bc (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else (* [comment removed for export] *)
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%lzb then
            match lin_lowbits_knB bc a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.
Local Close Scope lzb_scope.

Definition mkAndB (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_maskB bc a (k mod two64)%Z with
      | Some m => mkAnd0B bc a (ELit m)
      | None => mkAnd0B bc a b
      end
  | _ => mkAnd0B bc a b
  end.

Definition mkAndKB (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAndB bc x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAndB bc x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAndB bc a b
  | _, _ => mkAndB bc a b
  end.

Local Open Scope lzb_scope.
Definition or_disjointB (bc : bctx) (a b : expr) : bool :=
  match erangeB bc b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealignB bc a)))%lzb
  | None => false
  end.
Local Close Scope lzb_scope.

Definition mkOrB (bc : bctx) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjointB bc a b then mkAlu ALU_ADD a b
      else if or_disjointB bc b a then mkAlu ALU_ADD a b
      else (* [comment removed for export] *)
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndKB bc a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndKB bc b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryB bc e rest else
      if negb (evalS_def s e) then conc_tryB bc e rest else
      match erangeB bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryB bc e rest
                else conc_tryB bc e rest
            | None => conc_tryB bc e rest
            end
          else conc_tryB bc e rest
      | None => conc_tryB bc e rest
      end
  end.

Definition concretizeB (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_tryB bc e (nubE (subexprs e)).

Definition foldKB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeB bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeB bc e with Some v => ELit v | None => e end
         | None => match concretizeB bc e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

Local Open Scope lzb_scope.
Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
  match c with
  | BC_LTU => ltu
  | BC_GEU => option_map negb ltu
  | BC_LT | BC_GE =>
      match erangeB bc a, erangeB bc b with
      | Some (_, ah), Some (_, bh) =>
          if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%lzb
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      (* [comment removed for export] *)
      if (lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0B bc [(a, (-1)%Z)] [(b, 0%Z)])%lzb
      then Some (match c with BC_EQ => false | _ => true end)
      else
      (* [comment removed for export] *)
      if (if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then lin_ge0B bc [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.
Local Close Scope lzb_scope.

Definition decide_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match erangeB bc a, erangeB bc b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branchB bc c a b      (* [comment removed for export] *)
             end
           end
  end.

Definition mkSltB (bc : bctx) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branchB bc c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.

Definition mkAluK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAndB bc a b
               | ELit _, _ => mkAndKB bc b a      (* [comment removed for export] *)
               | _, _ => mkAndKB bc a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOrB bc a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrlB bc a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

Definition mkAluKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluK0B bc op a b).

Definition mkMdKB (bc : bctx) (op : mulop) (a b : expr) : expr :=
  match is_lit a, op, b with
  | None, M_REMU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKB bc ALU_AND a (ELit (2 ^ k - 1))
      | None => mkMd op a b
      end
  | None, M_DIVU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKB bc ALU_SRL a (ELit k)
      | None => mkMd op a b
      end
  | _, _, _ => mkMd op a b
  end.

Local Open Scope lzb_scope.
Definition zband32B (bc : bctx) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- 2 ^ 31) lo && Z.ltb hi (2 ^ 31))%lzb
  | None => false
  end.
Local Close Scope lzb_scope.

Definition mkAluwK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32 v)
      | None => match erangeB bc d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32B bc d then d else mkAluw op a b
                | None => if zband32B bc d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.

Definition mkAluwKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluwK0B bc op a b).

Definition extK0B (bc : bctx) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        match erangeB bc e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.

Definition extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v).

Local Open Scope lzb_scope.
Definition flat_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeB bc (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (two64))%lzb
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Fixpoint wr_coveredB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%lzb
          then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_coveredB bc rest a n
  | _ :: rest => wr_coveredB bc rest a n
  end.
Local Close Scope lzb_scope.

Definition storeok_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  if wr_coveredB bc (bc_fk bc) a n then [] else [SCStoreOk a n].

Definition conc_exprB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretizeB bc e with Some v => ELit v | None => e end
  end.

Definition enum_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretizeB bc e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

Definition to_saddrKB (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

Definition amo_alignedbB (bc : bctx) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_knB bc e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.

Definition amo_newvalB (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKB bc o old src end
  end.

Fixpoint log_lookupB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupB bc rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupB bc rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupB bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

Local Open Scope lzb_scope.
Fixpoint know_lookupA0B (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0B bc in
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
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%lzb then
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
Local Close Scope lzb_scope.

Definition know_lookupAB (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0B bc segs kn rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Definition sym_readB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupAB bc segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
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

Definition sym_stepB (bc : bctx) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
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
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod two64)) [] scr
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
      match sym_readB segs ss bc scr a n sx' with
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
        match sym_readB segs ss bc scr a n (amo_sx wd) with
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
                match sym_readB segs ss bc scr a n (amo_sx wd) with
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

Definition know_lookupB (segs : list Segment) (bc : bctx) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupAB bc segs (bc_fk bc) rb rk n sx hints acc.


Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition gran (a : Z) : Z := Z.shiftr a 12.
Definition is_lit0 (e : expr) : bool := match e with ELit 0 => true | _ => false end.
(* [comment removed for export] *)
Definition lit0_extent (K : kentry) : option (Z * Z) :=
  match K with
  | KWord (SA (ELit 0) kk) w _ => Some (kk, kk + Z.of_nat w)
  | KZero (SA (ELit 0) kk) (ELit l0) => Some (kk, kk + zmod64 l0)
  | KFill (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KBlob (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KImg lo hi => Some (lo, hi)
  | _ => None
  end.
(* [comment removed for export] *)
Definition ext_fits (s e : Z) : bool := if Z.ltb s e then Z.leb (gran (e - 1) - gran s) 1 else false.
Definition ext_has (s e g : Z) : bool := if Z.eqb g (gran s) then true else Z.eqb g (gran (e - 1)).
(* [comment removed for export] *)
Definition kx_wide0 (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => negb (ext_fits s e)
  | None =>
      match K with
      | KZero (SA kb _) _ | KFill (SA kb _) _ _ => true      (* [comment removed for export] *)
      | KBlob (SA kb _) _ _ => is_lit0 kb                    (* [comment removed for export] *)
      | _ => false
      end
  end.
(* [comment removed for export] *)
Definition kx_cand0 (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else true
  | None => kx_wide0 K
  end.
(* [comment removed for export] *)
Definition kx_candf (K : kentry) : bool :=
  match K with
  | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => negb (is_lit0 kb)
  | KZero _ _ | KFill _ _ _ => true
  | _ => false
  end.
(* [comment removed for export] *)
Definition kx_gkey (g : Z) : positive := match g with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Record kix : Type := KX {
  kx_kn : list kentry;                              (* [comment removed for export] *)
  kx_w0 : list (positive * kentry);                 (* [comment removed for export] *)
  kx_gran : ptree (list (positive * kentry));       (* [comment removed for export] *)
  kx_wf : list kentry                               (* [comment removed for export] *)
}.
Definition kx_bucket (t : ptree (list (positive * kentry))) (g : Z) : list (positive * kentry) :=
  match pt_get t (kx_gkey g) with Some b => b | None => [] end.
Definition kx_add (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
  pt_set (kx_gkey g) (x :: kx_bucket t g) t.
Fixpoint kx_build (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * list kentry :=
  match kn with
  | [] => ([], PTLeaf, [])
  | K :: rest =>
      let '(w0, gr, wf) := kx_build rest (Pos.succ i) in
      let wf' := if kx_candf K then K :: wf else wf in
      match lit0_extent K with
      | Some (s, e) =>
          if ext_fits s e then
            let g1 := gran s in let g2 := gran (e - 1) in
            let gr1 := kx_add g1 (i, K) gr in
            (w0, (if Z.eqb g1 g2 then gr1 else kx_add g2 (i, K) gr1), wf')
          else ((i, K) :: w0, gr, wf')
      | None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
      end
  end.
Definition mk_kix (kn : list kentry) : kix :=
  let r := kx_build kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
(* [comment removed for export] *)
Fixpoint kx_merge (l1 : list (positive * kentry)) : list (positive * kentry) -> list kentry :=
  match l1 with
  | [] => fun l2 => List.map snd l2
  | (p1, K1) :: r1 =>
      fix go (l2 : list (positive * kentry)) : list kentry :=
        match l2 with
        | [] => K1 :: List.map snd r1
        | (p2, K2) :: r2 => if Pos.ltb p1 p2 then K1 :: kx_merge r1 l2 else K2 :: go r2
        end
  end.
Definition kx_select (kx : kix) (rb : expr) (rk : Z) : list kentry :=
  if is_lit0 rb then kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx)
  else kx_wf kx.

Definition know_lookupA0I (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0B bc segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0B bc segs (kx_kn kx) rb rk n sx hints acc
  end.

(* [comment removed for export] *)
Lemma gran_div : forall a, gran a = a / 4096.
Proof. intros a. unfold gran. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma gran_mono : forall a b, a <= b -> gran a <= gran b.
Proof. intros a b H. rewrite !gran_div. apply Z.div_le_mono; lia. Qed.
Lemma gran_between : forall s e x,
  s <= x -> x < e -> ext_fits s e = true -> ext_has s e (gran x) = true.
Proof.
  intros s e x Hs He Hf. unfold ext_fits, ext_has in *.
  destruct (Z.ltb s e); [|discriminate]. apply Z.leb_le in Hf.
  pose proof (gran_mono s x Hs) as A. pose proof (gran_mono x (e - 1) ltac:(lia)) as B.
  destruct (Z.eqb_spec (gran x) (gran s)); [reflexivity|].
  destruct (Z.eqb_spec (gran x) (gran (e - 1))); [reflexivity|]. exfalso. lia.
Qed.
Lemma kx_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
  induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?kx_aluop_eqb_refl, ?kx_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.

Lemma rel_lit_same : forall rb rk rn kk kl,
  rel_lit rb rk rn rb kk kl =
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kl))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kl) rk)%bool then RDisjoint else RPartial.
Proof. intros. unfold rel_lit. rewrite kx_expr_eqb_refl. reflexivity. Qed.

Lemma rel_lit_other : forall rb rk rn kb kk kl,
  expr_eqb rb kb = false -> rel_lit rb rk rn kb kk kl = RUnknown.
Proof. intros rb rk rn kb kk kl H. unfold rel_lit. rewrite H. reflexivity. Qed.

Lemma is_lit0_eqb : forall rb kb, is_lit0 kb = true -> expr_eqb rb kb = is_lit0 rb.
Proof.
  intros rb kb H. destruct kb as [z| | | | | | |]; try discriminate. cbn in H.
  destruct z; try discriminate.
  destruct rb as [z'| | | | | | |]; cbn; try reflexivity; destruct z'; reflexivity.
Qed.
Lemma expr_eqb_lit0_l : forall kb, expr_eqb (ELit 0) kb = is_lit0 kb.
Proof. intros kb. destruct kb as [z| | | | | | |]; cbn; try reflexivity; destruct z; reflexivity. Qed.
Lemma is_lit0_true : forall e, is_lit0 e = true -> e = ELit 0.
Proof. intros e H. destruct e as [z| | | | | | |]; try discriminate. cbn in H. destruct z; try discriminate. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skip0 : forall bc segs K rest rk n sx acc,
  kx_cand0 (gran rk) K = false ->
  know_lookupA0B bc segs (K :: rest) (ELit 0) rk (S n) sx [] acc = know_lookupA0B bc segs rest (ELit 0) rk (S n) sx [] acc.
Proof.
  intros bc segs K rest rk n sx acc HC.
  cbn [know_lookupA0B].
  unfold two64.
  unfold kx_cand0, kx_wide0 in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try reflexivity.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC.
      rewrite rel_lit_same.
      change (if Z.leb kk rk then Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w) else false) with (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool in *; destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + Z.of_nat w)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + Z.of_nat w) rk) in HC; [discriminate|lia|lia|exact F].
      * change (if Z.leb (rk + Z.of_nat (S n)) kk then true else Z.leb (kk + Z.of_nat w) rk) with (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool in *; destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
      cbn in L. destruct z; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
      rewrite rel_lit_same.
      change (if Z.leb kk rk then Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64) else false) with (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool in *; destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * change (if Z.leb (rk + Z.of_nat (S n)) kk then true else Z.leb (kk + l0 mod 2 ^ 64) rk) with (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool in *; destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
      cbn in L. destruct z; try discriminate; destruct len; discriminate.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent is_lit0] in HC; rewrite ?zmod64_eq in HC; try discriminate.
      rewrite kx_expr_eqb_refl.
      destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
      destruct (Z.leb_spec kk rk) as [H1|H1]; [|reflexivity].
      destruct (Z.leb_spec (rk + Z.of_nat (S n)) (kk + (l0 mod 2 ^ 64))) as [H2|H2].
      * exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb_spec (kk + (l0 mod 2 ^ 64)) rk) as [H3|H3]; [reflexivity|].
        exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
    + rewrite expr_eqb_lit0_l, L. reflexivity.
  - (* [comment removed for export] *)
    destruct (ext_fits lo hi) eqn:F; [|discriminate].
    change (if Z.leb lo rk then Z.leb (rk + Z.of_nat (S n)) hi else false) with (Z.leb lo rk && Z.leb (rk + Z.of_nat (S n)) hi)%bool in *; destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat (S n)) hi)%bool eqn:E; [|reflexivity].
    exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    rewrite (gran_between lo hi rk) in HC; [discriminate|lia|lia|exact F].
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
      cbv zeta. rewrite rel_lit_same.
      change (if Z.leb kk rk then Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64) else false) with (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool in *; destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * change (if Z.leb (rk + Z.of_nat (S n)) kk then true else Z.leb (kk + l0 mod 2 ^ 64) rk) with (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool in *; destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
      cbn in L. destruct z; try discriminate; destruct len; discriminate.
Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skipf : forall bc segs K rest rb rk n sx acc,
  is_lit0 rb = false -> kx_candf K = false ->
  know_lookupA0B bc segs (K :: rest) rb rk n sx [] acc = know_lookupA0B bc segs rest rb rk n sx [] acc.
Proof.
  intros bc segs K rest rb rk n sx acc Hrb HC.
  cbn [know_lookupA0B]. unfold kx_candf in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try reflexivity; try discriminate.
  - (* [comment removed for export] *) destruct (is_lit0 kb) eqn:L; [|discriminate].
    rewrite rel_lit_other; [reflexivity|]. rewrite (is_lit0_eqb rb kb L). exact Hrb.
  - (* [comment removed for export] *) destruct (is_lit0 kb) eqn:L; [|discriminate].
    rewrite (is_lit0_eqb rb kb L), Hrb. reflexivity.
  - (* [comment removed for export] *) destruct rb as [z| | | | | | |]; try reflexivity. cbn in Hrb. destruct z; try reflexivity. discriminate.
Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_filter0 : forall bc segs l rk n sx acc,
  know_lookupA0B bc segs (List.filter (kx_cand0 (gran rk)) l) (ELit 0) rk (S n) sx [] acc
  = know_lookupA0B bc segs l (ELit 0) rk (S n) sx [] acc.
Proof.
  intros bc segs l rk n sx. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_cand0 (gran rk) K) eqn:HC.
  - (* [comment removed for export] *)
    cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0B_skip0 by exact HC. apply IH.
Qed.
Lemma know_lookupA0B_filterf : forall bc segs l rb rk n sx acc,
  is_lit0 rb = false ->
  know_lookupA0B bc segs (List.filter kx_candf l) rb rk n sx [] acc = know_lookupA0B bc segs l rb rk n sx [] acc.
Proof.
  intros bc segs l rb rk n sx acc Hrb. revert acc. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_candf K) eqn:HC.
  - cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0B_skipf by assumption. apply IH.
Qed.


(* [comment removed for export] *)
Fixpoint tagged (kn : list kentry) (i : positive) : list (positive * kentry) :=
  match kn with [] => [] | K :: rest => (i, K) :: tagged rest (Pos.succ i) end.
Definition all_gt (i : positive) (l : list (positive * kentry)) : Prop := Forall (fun t => (i < fst t)%positive) l.

Lemma filter_tagged_gt : forall P kn i j, (j < i)%positive -> all_gt j (List.filter P (tagged kn i)).
Proof.
  intros P kn. induction kn as [|K rest IH]; intros i j Hj; cbn [tagged List.filter]; [constructor|].
  destruct (P (i, K)).
  - constructor; [cbn; lia|]. apply IH. lia.
  - apply IH. lia.
Qed.

Lemma kx_merge_nil_l : forall l2, kx_merge [] l2 = List.map snd l2.
Proof. reflexivity. Qed.
Lemma kx_merge_cons_l : forall p K r1 l2,
  all_gt p l2 -> kx_merge ((p, K) :: r1) l2 = K :: kx_merge r1 l2.
Proof.
  intros p K r1 l2 H. destruct l2 as [|[p2 K2] r2]; cbn [kx_merge].
  - destruct r1 as [|[? ?] ?]; reflexivity.
  - apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p p2); [reflexivity|lia].
Qed.
Lemma kx_merge_cons_r : forall p K l1 r2,
  all_gt p l1 -> kx_merge l1 ((p, K) :: r2) = K :: kx_merge l1 r2.
Proof.
  intros p K l1 r2 H. destruct l1 as [|[p1 K1] r1]; cbn [kx_merge List.map snd]; [reflexivity|].
  apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p1 p); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma kx_merge_filters : forall (P Q : kentry -> bool) kn i,
  (forall K, P K = true -> Q K = false) ->
  kx_merge (List.filter (fun t => P (snd t)) (tagged kn i)) (List.filter (fun t => Q (snd t)) (tagged kn i))
  = List.filter (fun K => P K || Q K) kn.
Proof.
  intros P Q kn. induction kn as [|K rest IH]; intros i HPQ; [reflexivity|].
  cbn [tagged List.filter snd].
  destruct (P K) eqn:HP.
  - rewrite (HPQ K HP). cbn [orb]. rewrite kx_merge_cons_l; [rewrite IH; [reflexivity|exact HPQ]|].
    apply filter_tagged_gt. lia.
  - destruct (Q K) eqn:HQ; cbn [orb].
    + rewrite kx_merge_cons_r; [rewrite IH; [reflexivity|exact HPQ]|]. apply filter_tagged_gt. lia.
    + apply IH. exact HPQ.
Qed.

(* [comment removed for export] *)
Definition narrow_in (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else false
  | None => false
  end.
Lemma kx_cand0_split : forall g K, kx_cand0 g K = (narrow_in g K || kx_wide0 K).
Proof.
  intros g K. unfold kx_cand0, narrow_in, kx_wide0.
  destruct (lit0_extent K) as [[s e]|]; [|reflexivity].
  destruct (ext_fits s e); cbn [negb orb]; [rewrite Bool.orb_false_r|]; reflexivity.
Qed.
Lemma narrow_not_wide : forall g K, narrow_in g K = true -> kx_wide0 K = false.
Proof.
  intros g K. unfold narrow_in, kx_wide0. destruct (lit0_extent K) as [[s e]|]; [|discriminate].
  destruct (ext_fits s e); [reflexivity|discriminate].
Qed.

Lemma kx_gkey_inj : forall a b, kx_gkey a = kx_gkey b -> a = b.
Proof. intros [|a|a] [|b|b] H; cbn in H; congruence. Qed.
Lemma kx_bucket_add_same : forall g x t, kx_bucket (kx_add g x t) g = x :: kx_bucket t g.
Proof. intros. unfold kx_add, kx_bucket at 1. rewrite pt_gss. reflexivity. Qed.
Lemma kx_bucket_add_other : forall g g' x t, g <> g' -> kx_bucket (kx_add g' x t) g = kx_bucket t g.
Proof.
  intros g g' x t H. unfold kx_add. unfold kx_bucket at 1. rewrite pt_gso; [reflexivity|].
  intros E. apply H. apply kx_gkey_inj. exact E.
Qed.
Lemma kx_bucket_leaf : forall g, kx_bucket PTLeaf g = [].
Proof. intros. unfold kx_bucket. rewrite pt_get_leaf. reflexivity. Qed.

Lemma kx_build_spec : forall kn i w0 gr wf,
  kx_build kn i = (w0, gr, wf) ->
  w0 = List.filter (fun t => kx_wide0 (snd t)) (tagged kn i)
  /\ (forall g, kx_bucket gr g = List.filter (fun t => narrow_in g (snd t)) (tagged kn i))
  /\ wf = List.filter kx_candf kn.
Proof.
  induction kn as [|K rest IH]; intros i w0 gr wf H.
  - cbn in H. injection H as <- <- <-. split; [reflexivity|]. split; [intros g; rewrite kx_bucket_leaf; reflexivity | reflexivity].
  - cbn [kx_build] in H. destruct (kx_build rest (Pos.succ i)) as [[w0' gr'] wf'] eqn:Hb.
    destruct (IH (Pos.succ i) w0' gr' wf' Hb) as (A & B & C). clear IH.
    cbn [tagged List.filter snd].
    assert (NW : forall g, narrow_in g K = match lit0_extent K with Some (s, e) => if ext_fits s e then ext_has s e g else false | None => false end) by reflexivity.
    assert (WD : kx_wide0 K = match lit0_extent K with
                              | Some (s, e) => negb (ext_fits s e)
                              | None => match K with
                                        | KZero (SA kb _) _ | KFill (SA kb _) _ _ => true
                                        | KBlob (SA kb _) _ _ => is_lit0 kb
                                        | _ => false
                                        end
                              end) by reflexivity.
    destruct (lit0_extent K) as [[s e]|] eqn:HE.
    + destruct (ext_fits s e) eqn:HF.
      * (* [comment removed for export] *)
        match type of H with (_, ?G, _) = _ => set (gr1 := G) in H end.
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [exact A|]. split; [|rewrite C; reflexivity].
        intros g. rewrite NW.
        assert (STEP : kx_bucket gr1 g = if ext_has s e g then (i, K) :: kx_bucket gr' g else kx_bucket gr' g).
        { subst gr1. unfold ext_has. destruct (Z.eqb_spec (gran s) (gran (e - 1))) as [EQ|NE].
          - destruct (Z.eqb_spec g (gran s)) as [->|NE1].
            + rewrite kx_bucket_add_same. reflexivity.
            + rewrite kx_bucket_add_other by exact NE1. destruct (Z.eqb_spec g (gran (e - 1))); [congruence|reflexivity].
          - destruct (Z.eqb_spec g (gran s)) as [->|NE1].
            + rewrite kx_bucket_add_other by exact NE. rewrite kx_bucket_add_same. reflexivity.
            + destruct (Z.eqb_spec g (gran (e - 1))) as [->|NE2].
              * rewrite kx_bucket_add_same. rewrite kx_bucket_add_other by exact NE1. reflexivity.
              * rewrite kx_bucket_add_other by exact NE2. rewrite kx_bucket_add_other by exact NE1. reflexivity. }
        rewrite STEP, B. reflexivity.
      * (* [comment removed for export] *)
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity].
        intros g. rewrite NW, B. reflexivity.
    + clear WD. destruct (kx_wide0 K); injection H as <- <- <-.
      * split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
      * split; [exact A|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
Qed.

Lemma kx_select_eq : forall kn rb rk,
  kx_select (mk_kix kn) rb rk = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn else List.filter kx_candf kn.
Proof.
  intros kn rb rk. unfold kx_select, mk_kix.
  destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
  destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
  destruct (is_lit0 rb); [|exact C].
  rewrite B, A. rewrite (kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1%positive (narrow_not_wide (gran rk))).
  apply filter_ext. intros K. symmetry. apply kx_cand0_split.
Qed.

Theorem know_lookupA0I_eq : forall bc kn segs rb rk n sx hints acc,
  know_lookupA0I bc (mk_kix kn) segs rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
  intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I.
  destruct hints as [|h hs]; [|reflexivity]. destruct n as [|n]; [reflexivity|].
  rewrite kx_select_eq. destruct (is_lit0 rb) eqn:L.
  - apply is_lit0_true in L. subst rb. apply know_lookupA0B_filter0.
  - apply know_lookupA0B_filterf. exact L.
Qed.

(* [comment removed for export] *)
Definition know_lookupABI (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0I bc kx segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Lemma know_lookupABI_eq : forall bc kn segs,
  know_lookupABI bc (mk_kix kn) segs kn = know_lookupAB bc segs kn.
Proof.
  intros bc kn segs. bcfe. unfold know_lookupABI, know_lookupAB. rewrite know_lookupA0I_eq. reflexivity.
Qed.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Definition rprep : Type := (option (Z * Z) * list (saddr * expr))%type.
Definition mk_rprepB (bc : bctx) (rb : expr) (rk n : Z) : rprep :=
  (base_rangeB bc rb, fst (disj_sidesM bc (bc_fk bc) rb rk n [])).
Local Open Scope lzb_scope.
Definition ranges_apartRB (bc : bctx) (rp : rprep) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match fst rp, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%lzb%Z
      | _, _ => false
      end) then true
  else if in_sidesB bc (snd rp) b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Local Close Scope lzb_scope.
Lemma in_sidesB_kdisj : forall bc kn b1 k1 n1 b2 k2 n2,
  in_sidesB bc (disj_sidesB bc kn b1 k1 n1) b2 k2 n2 = kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sidesB kdisj_apartB]; try exact IH.
  destruct (sub_itvB bc b1 k1 n1 c1 m1), (sub_itvB bc b1 k1 n1 c2 m2); cbn [in_sidesB];
    destruct (sub_itvB bc b2 k2 n2 c2 m2) eqn:E2, (sub_itvB bc b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma ranges_apartRB_eq : forall bc b1 k1 n1 b2 k2 n2,
  ranges_apartRB bc (mk_rprepB bc b1 k1 n1) b1 k1 n1 b2 k2 n2 = ranges_apartB bc b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold ranges_apartRB, ranges_apartB, mk_rprepB. cbn [fst snd].
  rewrite disj_sidesM_eq, in_sidesB_kdisj. reflexivity.
Qed.
Fixpoint log_lookupP (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (orp : option rprep) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupP bc rest rb rk n sx hints acc orp
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let rp := match orp with Some rp => rp | None => mk_rprepB bc rb rk (Z.of_nat n) end in
          if ranges_apartRB bc rp rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupP bc rest rb rk n sx hints acc (Some rp)
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupP bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some rp)
          end
      end
  end.
Lemma log_lookupP_eq : forall bc log rb rk n sx hints acc orp,
  (orp = None \/ orp = Some (mk_rprepB bc rb rk (Z.of_nat n))) ->
  log_lookupP bc log rb rk n sx hints acc orp = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc orp Horp; [reflexivity|].
  cbn [log_lookupP log_lookupB].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH; exact Horp.
  - assert (E : match orp with Some rp => rp | None => mk_rprepB bc rb rk (Z.of_nat n) end = mk_rprepB bc rb rk (Z.of_nat n))
      by (destruct Horp as [-> | ->]; reflexivity).
    rewrite E, ranges_apartRB_eq.
    destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)).
    + apply IH. right; reflexivity.
    + destruct hints as [|[|] hs]; try reflexivity; apply IH; right; reflexivity.
Qed.

Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupP bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] None with   (* [comment removed for export] *)
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
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


Definition sym_stepBI (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
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
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod two64)) [] scr
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
      match sym_readBI segs ss bc kx scr a n sx' with
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
        match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
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
                match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
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


Lemma sym_readBI_eqf : forall segs ss bc, sym_readBI segs ss bc (mk_kix (s_know ss)) = sym_readB segs ss bc.
Proof. intros. bcfe. unfold sym_readBI, sym_readB. rewrite know_lookupABI_eq, log_lookupP_eq by (left; reflexivity). reflexivity. Qed.
Lemma sym_stepBI_eq : forall bc segs i ss scr,
  sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readBI_eqf. reflexivity. Qed.

Lemma coeffs_divkB_eqf : forall fk, coeffs_divkB (mkbc fk) = coeffs_divk fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.coeffs_divkB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.coeffs_divk); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf); constr:(@Corelib.Init.Datatypes.pair)|] [|@ts; @l; @p; @b; @e; @z; @IH; @rest; @a; @k; @a0; @m; @fk|] "#$0#.#O#7###,#4#$#&#+#%#6#'#D#(#8#:#-#O#1#=#)#@#*#K#E#L#N#M#A#3#2#5#>#I#J#H#P#Q#?#;#9#<#C#B#G#F+#I$#0&#J&#/&#K%#L%#M%#N%US#S/VS0FKUS##k#$#C#DUO#UPD#GVO#DVPGD#H&#JD$HJD%C$#j#$.#US10$JG#VS$C##N&#LD$NLD%C$##S%WS&8JG&$N#$S%N$%C$#k##(#k#%<#j#&>##I&#S'D$IS'D%C$#$EIG'LE(#MUS2S3US4##QVS(#H)%#*L#'#E(#MnC#$##C+#%#S)##nC#$##C##%#D#S*VRQH),#*L#'#E(#MVS+2#$QEJVS,$#%C+#j#'C#k#(KFUREUDH)8#*L#'#E(#MnC#$##C>#%#S)##nC#$##C##%#.#S*%C#.j#),#'HI(#MVREJ)s###*H#'#I(#MVS+(#VS,#s#,VS$C##EUS(#US5EZS-:90&$#&&IGZS-Cs#3=$#DXS6FKHJWS&s#V#G&*I#$EI$%C$#m#(#j#*s#;#j#+s#[#j#,K#j#-F#V#GDj#(K#j#)F#YS7FKs#F#Dj#.s#c#YS8s#ds#Ws#T#Dj#$s#d#YS.s#eCs#_s#^#j#/F#YS.Fs#fs#ds#c#j#0s#j##"). Qed.
#[export] Hint Rewrite coeffs_divkB_eqf : bceq.
Lemma lin_lowbits_knB_eqf : forall fk, lin_lowbits_knB (mkbc fk) = lin_lowbits_kn fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_lowbits_knB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_lowbits_kn); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.coeffs_divk); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.pageup_low); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.coeffs_divkB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.coeffs_divkB_eqf)|] [|@k; @ts; @m; @b; @x0; @x; @fk|] "##W#'#B#.###$#%#5#0#2#-#6#*#8#=#<#@#?#>#A#7#,#+#/#4#:#;#9#&#B#C#D#3#1$#A$ULS&US'Ck#$C##DUH#UID#EVH#DVIEDVS(CJUL#k#%#Gk#&C#UKFUS)S*US+#VM#EUNFWOC*#VD%#WPC,%VQ#'VRC#VS#F)nG#$##9'#%#$##WKS,+)nG#$##;##%#&#%WS$<%#j#'2#VM0DUNEWOC7#WKF%#WPC9%VQ#'VRC#VS#E)nG#$##s#&'#%#$##VS-s#'##FUS.#US/FZS0@?0&$#WH&EDWIFEDWS$s#.$#m#&#j#(C#YS%Cs#1s#+s#*#j#)J#YS%Js#2s#0s#/#j#*s#5##"). Qed.
#[export] Hint Rewrite lin_lowbits_knB_eqf : bceq.
Lemma lin_nowrap_lB_eqf : forall fk, lin_nowrap_lB (mkbc fk) = lin_nowrap_l fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrap_lB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_nowrap_l); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_range); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf)|] [|@ts; @e; @p; @lo; @hi; @x; @o; @x0; @fk|] "##N#'#?#0###-#$#%#.#5#=#1#3#*#/#6#7#,#+#9#:#;#<#&#>#?#@#A#4#2#8%#=$#>&UMRVHENUM#k#$#C#DUK#ULD#FVK#DVLFDVHEEUI#k#%N#UOG$DGFVS#S$FVS%DS&nC#$##C$#%###JnH%EE$#&CD#$%#'#(#nI$+$#)C'#%$#&##JUOS'$#GFVS()(nH%EE$#&CD#$%#'#(#nI$0$#)C%#%$#&##JWPC(#j#*0#$0FDnI$4$#)C##%$#&'#JVS)C##GUS*#US+GZS,76)&$#WK&FDWLGFDWPC$#m#&#j#+s#&#YQs#'CA@#j#)E#YQEs#(s#&s#%#j#,s#,##"). Qed.
#[export] Hint Rewrite lin_nowrap_lB_eqf : bceq.
Lemma mkSrlB_eqf : forall fk, mkSrlB (mkbc fk) = mkSrl fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSrlB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkSrl); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_nowrap_l); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_trivial); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.coeffs_div); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.unlin); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ldiv_terms); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lsplit_divc); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SRL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_nowrap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrapB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrap_lB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_nowrap_lB_eqf)|] [|@s; @ts; @c; @p; @lo; @hi; @x; @rts; @p0; @l1; @dts; @l0; @b; @e; @o; @x0; @fk|] "#$y#/#]#5#<#6#%#$#2###R#;#H#'#T#+#,#&#)#7#9#=#-#*#Y#Z#@#?#G#B#I#O#(#U#W#4#3#E#F#D#P#V#.#[#\#]#^#_#S#Q#K#L#J#X#8#A#C#M#N#>#:1#P$#Q&#R'#S%#T$#U%#V$#W$#X%#Y&#Z%#[&#+%#\)UHS4k#$EC)IUS##US$I)GVS##IVS$GI/ECUH#k#%#Dk#&E#US%F*FUS*#US+#US5S6US7#+#GWS,E,(VS-$#nD#$##D(#%###L)QVS.#FnD#$##D%#%###L,E2.&#*-+*%E5$#'#/77nD#$##D2#%#*#LVS/0/US8;%;;##nD#$##'&#%#%###Q$JM##S0$JR#/EEUN#*O,Es#$#VR#M)P%Es#'%M'#VS1%#US9+nD#$##+(#%#$##+s#$S&&G#&I$VS2$#-&O%Es#1&#'##S&$JS:#nD#$##C(#%#%##nK%EE$#'CI#$%#(#)##S'$JO#nN$:$#*C0#%$#'%##nH$s#;$#+CF#%#<%#,#-#nH$s#<$#.CG#%#?%#'#/#nK%s#<s#<$#*CB#$%#.#+#nD#$##Cs#.#%#s#)##(s#8s#3VS(QF($#(s#;$nD#$##s#-##%#s#+#s#)WS%PAMVS)P>nD#$##s#%$#%###=nN$s#'$#*C##%$#'2#0nH$s#H$#+CF#%#s#)%#,#-#nH$s#I$#.CG#%#s#,%#'#/#nK%s#Is#I$#*C)#$%#.#+#nD#$##C,#%#s#6##.C0#j#0s#J#k#1CDUS(FUIFnD#$##Ds#D#%###LnD#$##Ds#K#%#$#LnD#$##s#=##%#s#;#s#9nD#$##s#32#%#s#,#s#+nN$s#5$#*C##%$#'@#>nH$s#V$#+CF#%#s#7%#,#-#nH$s#W$#.CG#%#s#:%#'#/#nK%s#Ws#W$#*C'#$%#.#+#nD#$##C*#%#s#D##.C#1j#0/#k#1Cs#;US)FnD#$##Ds#Q#%#@#LnD#$##Ds#X#%#A#LnD#$##s#J##%#s#H#s#FURs#:nD#$##s#A@#%###s#9nN$s#C$#*C##%$#'s#.#s#,nH$s#d$#+CF#%#s#E%#,#-#nH$s#e$#.CG#%#s#H%#'#/#nK%s#es#e$#*C(#$%#.#+#nD#$##C+#%#s#R##.C#?j#2/#*GUS*#US+#+s#dIWS,Es#m&VS-$#(&#VS(FG($#,Es#r+&#)-*)%Es#u$#'#(.)VS/.-nD#$##s#d$#%###s#`#F$JQ##M$JS0#*S',Es$##WS%O#M%Es$%$M'#VS)O#nD#$##s#d&#%###s#\+s#}P&G#&I$VS2$#-&O%Es$.&#'##P$JS&#nD#$##C(#%#%##nK%EE$#'CI#$%#(#)##R$JS'#nN$s#s$#*C0#%$#'%##nH$s$8$#+CF#%#8%#,#-#nH$s$9$#.CG#%#;%#'#/#nK%s$9s$9$#*C>#$%#.#+#nD#$##Cs#'#%#B##VS;C#)FUS1#US<F0s#Bs#As#5&$#US.&US=F0s#Ss#Rs#F%$#US>)US?F0s$Cs$Bs#W%$#WS#,GIWS$FGI.C$#m#&#j#3E#YS3ECs$Ns$M#j#*C#YS3Cs$Us$Ss$R#j#4s$W##"). Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : forall fk, lowbitsB (mkbc fk) = lowbits fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lowbitsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lowbits); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_ind); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EVar); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_lowbits_kn); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_lowbits_knB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_lowbits_knB_eqf); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EAlu); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.lxor); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EAluw); constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EMd); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EMdw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EExt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EBlob)|] [|@j; @e; @x; @z; @k; @o; @n; @y; @v; @b; @c; @op0; @a0; @b0; @sx; @lo; @e0; @i; @op; @IHe2; @e2; @IHe1; @e1; @a1; @IHe; @fk|] "#)>#0#_#7#N#$###&#8#'#6#%#(#)#*#+#,#S#\#-#G#.#/#9#;#M#>#B#W#X#Y#Z#O#J#L#Q#3#4#E#F#D#U#V#^#<#K#=#I#@#A#:#5#?#T#]#C#H#P#R#[#_#`#aD#M%#N&#@%#A&#O)#P%#7%#8%#Q%#8&#B%#R$#7&#S(#T%#&$#C&#&%#U&#V&#W%#X$#A$#@$#B$#Y$#C$#Z$#%$#[&#\&#]'#^'US4S5UHCk#$C#.FUS'#US(F.K)#F*KF$)$#j#%J#US*F)(#*K$+ES+US6S7US8#7#F+&#(C#15#.GUS*E/$#F,G$F$:$#m#(#j#&C#0C=21#j#'C#8F);#*K$k#(CBk#%J#9G.I8K-$##E#(CS)4&EnD#$##s#+%#%#$##%I(#E#&I*EnD#$##s#/$#%#(##$s#0'#j#)0#k#%JC:G20#E#nD#$##s#6##%#/#*$s#7#*j#'(#8E%G##F#&G%FnD#$##s#=$#%#6##1s#>#;s#+<G'10+%$#=s#.>G's##B5%$#/s#1.F,G/F$s#G$#m#&#j#&C#0Cs#Js#,s#+#j#*S$#)s#8F*GF$s#M$#.L)#F*LF$s#Q$#.M5IGE)$#*M$*NI2E.P/#IKVS9EF7s#MG+$#(C#5NMI-)##K#3+%KnD#$##s#c$#%#s#<##nH$C$#&s#d,#%$#+(##.O5MLG-$##E#3&%EnD#$##s#j$#%#s#C##nH$C$#&s#k5#%$#&)##VS:EF+#3(C#nH$C$#&s#o7#%$#+##.nH$C$#&s#p:#%$#&##(?K+s#e8VS,F#(C#nH$C$#&s#u&#%$#,##4.S%5POM-$##I#3&%InD#$##s#{$#%#s#T##.S&5S#PN-$##L#3&%LnD#$##s$%$#%#s#Z##nJ#$#-s$&G#+$#./$#*A&#/#0#1)&#/#0#1)&#/#0#1)&#/#0#1)'#2#3#*#4#'#2#(#5#*#VS-F3(C#nH$C$#&s$)6#%$#,##s#$nJ#$#-s$*G#+$#.#$#*s#%&#/#0#1-&#/#0#1-&#/#0#1-&#/#0#1-'#2#3#*#4''#2#(#5#*'+FS+7s#yK+$#VS.#S)VS/F;(C#nH$C$#&s$1>#%$#,##s#,nD#$##s$2&#%#s#g##nJ#$#-s$3G#+$#.#$#*s#.&#/#0#16&#/#0#16&#/#0#16&#/#0#16'#2#3#*#40'#2#(#5#*0nQ#$#6s$4M#-#s#'#B#s#(#s#(#s#(#0#s#(#s#(#,##,OLE,PIK%Ps#6#K#&Ps#8KnD#$##s$:$#%#s#o##nH$C$#&s$;'#%$#+s#;##%Os#4#E#&Os#6EnD#$##s$?$#%#s#t##nH$C$#&s$@-#%$#&'##nH$C$#&s$A-#%$#+s#1#)nH$C$#&s$B/#%$#&##%,PMKnH$C$#&s$D##%$#,s#.#,%S%s#,#I#&S%s#.InD#$##s$H$#%#s#}##%S&s#*#L#&S&s#,LnD#$##s$L$#%#s$%##nJ#$#-s$MG#+$#.+$#*5&#/#0#1'&#/#0#1'&#/#0#1'&#/#0#1''#2#3#*#4#'#2#(#5#*#nH$C$#&s$N-#%$#,s#(#6nJ#$#-s$OG#+$#.#$#*7&#/#0#1)&#/#0#1)&#/#0#1)&#/#0#1)'#2#3#*#4%'#2#(#5#*%nH$C$#&s$P/#%$#,B#8nD#$##s$Qs#%#%#s$*##nJ#$#-s$RG#+$#.#$#*:&#/#0#1,&#/#0#1,&#/#0#1,&#/#0#1,'#2#3#*#4('#2#(#5#*(nQ#$#6s$SM#-#5#3#6#6#6#(#6#6#&##$s$TB#j#)s$T#*NKnH$C$#&s$Ws#D#%$#+s#W#s#RnH$C$#&s$Xs#%#%$#&##s#LnH$C$#&s$Ys#F#%$#+s#I#s#TnH$C$#&s$Zs#'#%$#&##s#NnH$C$#&s$[:#%$#,s#E#s#VnJ#$#-s$\G#+$#.#$#*s#W&#/#0#1s#?&#/#0#1s#?&#/#0#1s#?&#/#0#1s#?'#2#3#*#4s#9'#2#(#5#*s#9nH$C$#&s$]<#%$#,s#7#s#XnJ#$#-s$^G#+$#.#$#*s#Y&#/#0#1s#A&#/#0#1s#A&#/#0#1s#A&#/#0#1s#A'#2#3#*#4s#;'#2#(#5#*s#;nH$C$#&s$_>#%$#,s#1#s#ZnD#$##s$`s#4#%#s$9##nJ#$#-s$aG#+$#.#$#*s#\&#/#0#1s#D&#/#0#1s#D&#/#0#1s#D&#/#0#1s#D'#2#3#*#4s#>'#2#(#5#*s#>nQ#$#6s$bM#-#,#*#s#V#s#V#s#V#(#s#V#s#V#&##$s$c#2j#)s$c#9NVEs#eKnD#$##s$gs#d#%#s$@##nH$C$#&s$hs#4#%$#+s#h##4s#aEnD#$##s$js#`#%#s$C##nH$C$#&s$ks#8#%$#&%##nH$C$#&s$ls#8#%$#+s#\#'nH$C$#&s$ms#:#%$#&##%nH$C$#&s$ns#-#%$#,s#X#)VGs#VInD#$##s$ps#U#%#s$I##VIs#RLnD#$##s$rs#Q#%#s$K##nJ#$#-s$sG#+$#.'$#*.&#/#0#1%&#/#0#1%&#/#0#1%&#/#0#1%'#2#3#*#4#'#2#(#5#*#nH$C$#&s$ts#3#%$#,s#N#/nJ#$#-s$uG#+$#.#$#*0&#/#0#1'&#/#0#1'&#/#0#1'&#/#0#1''#2#3#*#4%'#2#(#5#*%nH$C$#&s$vs#5#%$#,s#H#1nD#$##s$ws#K#%#s$P##nJ#$#-s$xG#+$#.#$#*3&#/#0#1*&#/#0#1*&#/#0#1*&#/#0#1*'#2#3#*#4('#2#(#5#*(nQ#$#6s$yM#-#0#.#1#1#1#(#1#1#&##$s$z#s#)j#)s$Z#:N?s#|#K#nD#$##s%###%#s$X#s#HnH$C$#&s%$s#L#%$#+s$$##2s#y#E#nD#$##s%'##%#s$\#s#GnH$C$#&s%(s#Q#%$#&&##nH$C$#&s%)s#Q#%$#+s#u#(nH$C$#&s%*s#S#%$#&##%nH$C$#&s%+s#F#%$#,s#q#*UGs#o#I#nD#$##s%.##%#s$c#s#EUIs#l#L#nD#$##s%1##%#s$f#s#DnJ#$#-s%2G#+$#.)$#*1&#/#0#1&&#/#0#1&&#/#0#1&&#/#0#1&'#2#3#*#4#'#2#(#5#*#nH$C$#&s%3s#N#%$#,s#i#2nJ#$#-s%4G#+$#.#$#*3&#/#0#1(&#/#0#1(&#/#0#1(&#/#0#1('#2#3#*#4%'#2#(#5#*%nH$C$#&s%5s#P#%$#,s#c#4nD#$##s%6s#f#%#s$k##nJ#$#-s%7G#+$#.#$#*6&#/#0#1+&#/#0#1+&#/#0#1+&#/#0#1+'#2#3#*#4('#2#(#5#*(nQ#$#6s%8M#-#2#0#3#3#3#(#3#3#&##$s%9#s#Dj#'s$f#,NIF,OGE+s$@s#o(C#nH$C$#&s%?%#%$#+##s#^5LIK%N##F#&N%FnD#$##s%D$#%#s$y##nH$C$#&s%E,#%$#&(##+s$8s#x(C#nH$C$#&s%H.#%$#+##s#gnH$C$#&s%I0#%$#&##'+s%=s#|VS,F#(C#nH$C$#&s%Ms#v#%$#,##s#l5ONL%S###G#&S#%GnD#$##s%R$#%#s%+##nJ#$#-s%SK#+$#.($#*s#r&#/#0#1#&#/#0#1#&#/#0#1#&#/#0#1#'#2#3#*#4s#i'#2#(#5#*s#iVS-F,(C#nH$C$#&s%Vs$##%$#,##s#unJ#$#-s%WK#+$#.#$#*s#v&#/#0#1'&#/#0#1'&#/#0#1'&#/#0#1''#2#3#*#4s#m'#2#(#5#*s#m7s%IE+s$0#VS.#S)VS/F3(C#nH$C$#&s%]s$*#%$#,##s#|nD#$##s%^&#%#s%7##nJ#$#-s%_K#+$#.#$#*s#~&#/#0#1/&#/#0#1/&#/#0#1/&#/#0#1/'#2#3#*#4s#u'#2#(#5#*s#unQ#$#6s%`L#-#=#9#>#>#>#/#>#>#+##1s%a#.N;#<N's%5s#Gs#-&$#=&>N's%Gs#as#K%$#))K's%is#rs#d$#E)+I's%ks$ss#u$#G/-s#/F,Ns#0F$s%o$#m#&#j#&C#0Cs%rs${s$z#j#7s%##j#8J#j#9s%)#j#:J#j#6Q#@IGE)s%(#*M$@MLG-s$u##E#4%EnD#$##s&#$#%#s%X##%O'#E#&O)EnD#$##s&'$#%#s%\##$s&('#j#)s%d#2-#E#nD#$##s&,##%#s%a#($s&-#(j#'s%Z#@LIK%N##F#&N%FnD#$##s&3$#%#s%h##1s&4#'s%as#s)#s#0s#/'s%qs$//#s#.s#-/s#3*F,N+F$s&9$#m#&#j#&C#0Cs&<A@#j#7s%I#j#8J#j#9s%O#j#:J#j#6Q#6IGE)s%N#*M$VS;EF+#s%H(C#6NMI-s%N##K#3s%P%KnD#$##s&L$#%#s&%##nH$C$#&s&Ms%:#%$#,(##nD#$##s&Ns$~#%#s&'##6POM-s%8##I#3s%:%InD#$##s&S$#%#s&,##6S#PN-s%7##L#3s%9%LnD#$##s&X$#%#s&1##nJ#$#0s&YL#+$#.-$#*/&#/#;#-(&#/#;#-(&#/#;#-(&#/#;#-('#2#3#*#4#'#2#(#5#*#6MLG-s%T##E#3s%V%EnD#$##s&^$#%#s&7##nR#$#6s&_M#+#(##############%P:#K#&P<KnD#$##s&c$#%#s&<##nH$C$#&s&ds%0#%$#,?##nD#$##s&es%9#%#s&>##%S%9#I#&S%;InD#$##s&i$#%#s&B##%S&8#L#&S&:LnD#$##s&m$#%#s&F##nJ#$#0s&nL#+$#.+$#*-&#/#;#-'&#/#;#-'&#/#;#-'&#/#;#-''#2#3#*#4#'#2#(#5#*#%O7#E#&O9EnD#$##s&r$#%#s&K##nR#$#6s&sM#+#'##############$s&t7#j#)s&t#VEs#0KnD#$##s&ws#/#%#s&P##nH$C$#&s&xs%D#%$#,s#3##nD#$##s&ys%M#%#s&R##VGs#-InD#$##s&{s#,#%#s&T##VIs#*LnD#$##s&}s#)#%#s&V##nJ#$#0s&~L#+$#.'$#*)&#/#;#-%&#/#;#-%&#/#;#-%&#/#;#-%'#2#3#*#4#'#2#(#5#*#4s#'EnD#$##s'$s#&#%#s&Y##nR#$#6s'%M#+#%##############$s'&#1j#)s&b#?s#>#K#nD#$##s'*##%#s&_#s#&nH$C$#&s'+s%S#%$#,s#B##nD#$##s',s%\#%#s&a##UGs#<#I#nD#$##s'/##%#s&d#s#%UIs#:#L#nD#$##s'2##%#s&g#s#$nJ#$#0s'3L#+$#.)$#*+&#/#;#-&&#/#;#-&&#/#;#-&&#/#;#-&'#2#3#*#4#'#2#(#5#*#2s#8#E#nD#$##s'6##%#s&k#s##nR#$#6s'7M#+#&##############$s'8#s##j#'s&e#+s#Ss%l(C#nH$C$#&s'<s$^#%$#,##s#(nD#$##s'=s$A#%#s&r##6ONL%S###G#&S#%GnD#$##s'B$#%#s&w##nJ#$#0s'CI#+$#.($#*s#/&#/#;#-#&#/#;#-#&#/#;#-#&#/#;#-#'#2#3#*#4s#8'#2#(#5#*s#86LIK%N##F#&N%FnD#$##s'H$#%#s&}##nR#$#6s'IL#+#(##############1s'J#'s&ws%-4#s$Fs$E's'+s%Es#'#s$Ds$C's'Ls%Us#6#s$BE/s$J,F,N-F$s'P$#m#&#j#&C#0Cs'Ss#ns#m#j#7s&`#j#8J#j#9s&f#j#:J#j#6R#AIGE)s&e#*M$AMLG-s&V##E#4%EnD#$##s'`$#%#s'9##%O'#E#&O)EnD#$##s'd$#%#s'=##$s'e'#j#)s'E#2-#E#nD#$##s'i##%#s'B#($s'j#(j#'s';#ALIK%N##F#&N%FnD#$##s'p$#%#s'I##1s'q#'s'Bs%T)#s$ms$l's'Rs%l/#s$ks$j/s$p*F,N+F$s'v$#m#&#j#&C#0Cs'yA@#j#7s'*#j#8J#j#9s'0#j#:J#j#6R#BIGKE)s'/#*M$BMLIG-s&|##E#4%EnD#$##s(*$#%#s'_##%O'#E#&O)EnD#$##s(.$#%#s'c##$s(/'#j#)s'k#2-#E#nD#$##s(3##%#s'h#($s(4#(j#'s'a#BLIGK%N##F#&N%FnD#$##s(:$#%#s'o##1s(;#'s'hs%z)#s%7s%6's'xs&6/#s%5s%4/s%:*F,N+F$s(@$#m#&#j#&C#0Cs(CA@#j#<s'P#j#%J#j#*S$#j#3S$#j#2D#CGKEF)s'Y#*L$9MCLIGK-s%J##E#4%EnD#$##s(Q$#%#s(*##%N'#E#&N)EnD#$##s(U$#%#s(.##$s(V'#j#)s(6#:M2.#E#nD#$##s([##%#s(4#)$s(\#)j#'s(-#CIGKE%M##F#&M%FnD#$##s(b$#%#s(;##1s(c#;s'o<M's(60+%$#=s'r>M's(H?4%$#/s'u.F,M/F$s(l$#m#&#j#&C#0Cs(os#'s#&#j#*S$#j#5C#j#(S$#j#2D#^S<s(ks(Xs(+s%[s%5s#zs#Ts#.#Fj#%J#0Js(us(ss(r#j#=s(x##"). Qed.
#[export] Hint Rewrite lowbitsB_eqf : bceq.
Lemma lsplit_divB_eqf : forall fk, lsplit_divB (mkbc fk) = lsplit_div fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lsplit_divB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lsplit_div); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf)|] [|@ts; @l; @p; @d; @r; @e; @z; @IH; @rest; @a; @k; @a0; @m; @fk|] "#$?#0#O###$#(#6#8#C#%#)#7#+#,#F#.#'#9#;#&#-#P#3#>#*#/#M#G#O#B#5#4#?#K#L#J#Q#@#<#:#=#N#A#E#D#I#H-#G$#2&#H&#I'#1&#J&#K%#L%#M%#N%US&S/VKFGUS&#VK##k#$$##CUQ#URC#DVQ#CVRDC#S#'#IC$S#IC%-$#j#$/#US01$ID#VS'1##E'#PC$EPC%5$##J(9ID'$E#$JE$%:$#k##(#k#%=#j#&?##L'#S(C$LS(C%A$#$MLD)JO*#NUS1S2US3##S)VS*#E+%#,J#)#O*#NnH#$##H+#%#S+##&FGJE(s#1#D&s#1s#1#C(s#3%C&s#3s#3D#nH#$##s#3(#%#%##nK%s#5s#5$#&s#4C#$%#'#(#$S$MIVS%S)E+3#,J#)#O*#NVS,9#nH#$##s#<##%#.#,nK%s#>s#>$#&s#=*#$%#'#(#%s#>,#j#&s#?#k#)GFUS%MUIE+?#,J#)#O*#NnH#$##Hs#%#%#S+##nH#$##s#H##%#:#8nK%s#Js#J$#&s#I6#$%#'#(#%s#J#/j#*-#)ES$*#NVS%OP+s#+#,E#)#S$*#NVS,(#&FGEP(s#W#D&s#Ws#W#C(s#Y%C&s#Ys#YD#nH#$##s#Y(#%#%##nK%s#[s#[$#&s#Zs#:#$%#'#(#VS's#[##MUS*#US4MZS-A@6&$#'&LDZS-s#as#As#$$#C&FGS#I(s#e#D'*L#$ML$%s#f$#m#(#j#+s#I#j#,s#j#j#-G#j#.F#V#DCj#)G#j#*F#YS5FGs#T#Cj#/s#r#YS6s#ss#es#b#Cj#$s#s#YS.s#ts#ss#ms#l#j#0F#YS.Fs#ts#rs#q#j#1s#y##"). Qed.
#[export] Hint Rewrite lsplit_divB_eqf : bceq.
Lemma and_high_splitB_eqf : forall fk, and_high_splitB (mkbc fk) = and_high_split fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.and_high_splitB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.and_high_split); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.unlin); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_AND); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf)|] [|@rts; @dts; @c; @j; @e; @p; @lo; @hi; @x; @o; @x3; @x2; @x1; @x0; @fk|] "#$5#,#L#3###2#$#%#&#(#'#5#7#4#9#)#J#I#:#/#*#C#G#E#K#;#0#A#B#@#+#L#M#N#8#=#<#H#6#1#?#>#D#F,#C'#D$#E&#F$#G(#H%#I%#J%#K%US#S*VMCEUS##k#$#Ek#%$#k#&C#k#'C#&DUK#ULD&FVK#DVLFD&GWK#FDWLGFD&HXK#GFDXLHGFD&JYK#HGFDYLJHGFDVMCCUN#k#(E#URIUS+S,US-#(#J)H##C>#F$#UD#((S$*F#*D$VS%$#)O&+O#VS&'(VS'$##Cs#)#I$##Cs#+'I$##Cs#-*J$#%P#S.%Q&#nS(#$##E/#%#)##nM%CC$#)ED#$%#*#+#+H8#Cs#4#G$#%P9I%Q$#nN$s#$$#,E:#%$#)(##VRO<nN$s#&$#,E##%$#)*#%WS)E%#j#-s#&#(s#$H)G##Cs#?#D$#VRI#(s#)O*F#*D$VS%$#)I&+I#VS&'(VS'$##Cs#J#J$##Cs#L'J$##Cs#N*H$#%P#S$%Q&#nS(#$##E/#%#)##nM%CC$#)ED#$%#*#+#+G8#Cs#U#F$#%P9J%Q$#nN$s#E$#,E:#%$#)(##VS/E#&IUS0#US1IZS2s#Hs#Gs#$&$#ZK&JHGFDZLIJHGFDWS)E$#m#&#j#.s#c#'s#dEs#Rs#Q#j#/s#e#'s#fs#es#Ws#V#j#0C#'Cs#fs#\s#[#j#1C#'Cs#gs#as#`#j#,E#'Es#hs#fs#e#j#2s#o##"). Qed.
#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Lemma and_low_splitB_eqf : forall fk, and_low_splitB (mkbc fk) = and_low_split fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.and_low_splitB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.and_low_split); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.unlin); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_AND); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf)|] [|@rts; @c; @j; @e; @p; @lo; @hi; @x; @o; @x2; @x1; @x0; @fk|] "##{#+#I#2#1###$#'#%#&#4#6#3#8#G#9#(#.#)#B#E#D#H#:#/#@#A#?#*#I#J#K#7#<#;#5#>#=#C#F#0+#A'#B$#C$#D%#E%#F%#G&#H(UQS(VLCDUQ#k#$#Dk#%C#k#&C#%EUJ#UKE%FVJ#EVKFE%HWJ#FEWKHFE%IXJ#HFEXKIHFEVLCCUM#k#'D#UOGUS)S*US+#&#I'H##C:#F$#UE#&(R(F#(E$VS#$#'P&VS$&'VS%$##Cs#$#G$##Cs#&'G$#)N#S,nS&#$##D+#%#&##nL%CC$#(DE#$%#)#*#)N2GnM$<$#+D2#%$#($##VOP4nM$>$#+D##%$#(&#%WS'D%#j#,>#&<H'F##Cs#3#E$#VOG#&AP(F#(E$VS#$#'G&VS$&'VS%$##Cs#=#I$##Cs#?'I$#)N#RnS&#$##D+#%#&##nL%CC$#(DE#$%#)#*#)N2InM$s#5$#+D2#%$#($##VS-D#%GUS.#US/GZS0s#8s#7<&$#YJ&IHFEYKGIHFEWS'D$#m#&#j#-s#O#*s#PDs#Bs#A#j#.C#*Cs#Qs#Gs#F#j#/C#*Cs#Rs#Ls#K#j#+D#*Ds#Ss#Qs#P#j#0s#Y##"). Qed.
#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Lemma narrow_maskB_eqf : forall fk, narrow_maskB (mkbc fk) = narrow_mask fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.narrow_maskB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.narrow_mask); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ctz64); constr:(@Stdlib.ZArith.BinInt.Z.log2); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf)|] [|@k'; @e; @x; @h; @o; @x0; @fk|] "##s#'#G###.#%#6#$#/#0#2#-#4#8#<#9#A#C#D#B#5#,#*#+#>#E#&#G#H#I#3#7#=#;#F#1#?#:#@+#?%#@$#A%#B%#C$#D$#E%#F$US&S'UHDk#$D#'CUI#UJC'GVI#CVJGCk#%K*ULE#MG$S(UN#(G%$#)G#*#%'#VO%#nF#$##F+#%###P$+$#$#$#$#UN##,#nF#$##F*#%###PUCE(E%4#)E#*#%7##C#VQR'VS#D#US)DnF#$##s#(&#%#$##nH$D$#&s#)-#%$#'##$nF#$##s#*/#%###%&A9&#2VLS*EnH$D$#&s#.##%$#'(#)nF#$##s#/%#%###*WS$s#0(#j#(s#)##MC(C%s#(#)C#*#%s#+#VO%#&)##&A&$#VLEG#Cs#,VQRs#0VS#D#nF#$##s#@%#%###;nH$D$#&s#A'#%$#'##<nF#$##s#B)#%###=VS+s#C#'EUS,#US-EZS.s#?s#>8&$#WI&GCWJEGCWS$s#J$#m#&#j#)D#YS%Ds#Ms#Gs#F#j#&K#YS%Ks#Ns#Ls#K#j#*s#Q##"). Qed.
#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Lemma mkAnd0B_eqf : forall fk, mkAnd0B (mkbc fk) = mkAnd0 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAnd0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAnd0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.and_low_split); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.log2); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_trivial); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.coeffs_divkB); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.unlin); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lsplit_divB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkMd); constr:(@LinuxProcessSemantics.Riscv.Instr.M_MUL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSrlB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.and_high_splitB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lowbitsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_AND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_lowbits_knB); constr:(@Corelib.Init.Datatypes.option); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.coeffs_divk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lsplit_div); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkSrl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.and_high_split); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lowbits); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_lowbits_kn); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.coeffs_divkB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_lowbits_knB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSrlB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lowbitsB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lsplit_divB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.and_high_splitB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.and_low_splitB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.and_low_splitB_eqf)|] [|@b; @rts; @c; @j; @bk; @p0; @l1; @dts; @p; @l0; @x; @l; @v; @k; @n; @op; @a0; @b0; @sx; @lo; @e; @i; @ts; @m; @o; @s; @a; @z; @x0; @fk|] "#&|#.#q#4#=#9#%#&#$#1#`#'#:#(###@#*#V#+#H#)#^#5#7#;#T#X#-#,#_#c#d#g#h#E#>#J#L#K#O#N#P#Y#[#\#e#f#i#3#2#S#a#j#k#l#m#n#o#p#q#r#s#I#<#U#8#6#A#F#b#?#D#]#W#B#M#R#Q#C#G#Z:#^%#_&#`&#a)#b$#c%#d$#e%#f%#g$#h&#i$#j%#k$#l&#m'#M&#N&#O&#(%#n$#o%#p%UISAk#$CC'NUS&#US'N'HVS&#NVS'HNVLECUI#k#%#Ck#&E#k#'E#k#(C#US(F(NO+O#,S27#)%/$#VS3'#,',#,#,#,#7#8+#nD#$##D*#%###S#'KVS4#G#/#0GUS5#US6#WS7E=%WS8)3#nD#$##D%#%###S#1E@((#6+$#2Es###(US9#VLs#%s#%USBs#'2s#'s#'#,WS)3=-nD#$##&0#%#$##(FO+O#)#/s#$#.#'S$WS*#M&%Q%#(KO+O#)#/s#,#.#'RWS*#P&%Q%#'S+(S$O+O#)#0S,1Es#?#ZS:(R%#MKnI$s#B$#%CF#%#*%#)#*#nI$s#C$#+CH#%#3%#,#-#nL%s#Cs#C$#.C<#$%#+#%#nD#$##Cs#'#%#B##nD#$##Cs#.#%#G##7S29s#A#)#/s#@#VS3%#8%s#9nD#$##D$#%###S##'s#7.S;WS<s#:G).N-S%GFWS-s#=G,WS)s#>,s#8-S%MK-S%PS$9=2)#XPR#;KnI$s#Z$#%CF#%#&%#)#*#nI$s#[$#/CH#%#(%#,#-#nL%s#[s#[$#.C*#$%#/#%#nJ$E$#.C,#%$#0.##nD#$##Cs#D#%#.##nJ$E$#.C1#%$#00##nD#$##C4#%#3##8S;s#Z)s#[9#>##s#QnD#$##D&#%###S#nD#$##D##%#s#K#S#WS-s#QG&(HOVSCN#.#nJ$E$#.C&#%$#0##;nD#$##C(#%###<nD#$##CB#%#/##nD#$##Cs#Y#%#s#*##-S%S$MnC#$#$CH#+$#1$$#2@&#3#4#5=&#3#4#5=&#3#4#5=&#3#4#5='#6#7#2#8#'#6#1#9#2#*s#ds#]VS.KG#s#h#WS/Ks#hs#X*s#Z#3Ks#js#ZnD#$##s#Ss#]#%#s#Q##4S$Ms#M%Qs#L#4RPs#G%Qs#F#ZS0S+Rs#@s#>MKnI$s#}$#%CF#%#$%#)#*#nI$s#~$#+CH#%#'%#,#-#nL%s#~s#~$#.C*#$%#+#%#nD#$##C-#%#s#]##nD#$##C0#%#G##*s#9s#8#s#<3WS1KGs#=5KGs#>3Ks#>s#jYS(S+Rs#1s#IKnI$s$,$#%CF#%#s#4%#)#*#nI$s$-$#/CH#%#s#6%#,#-#nL%s$-s$-$#.C&#$%#/#%#nJ$E$#.C(#%$#0s#<##nD#$##Cs#r#%#s#<##nJ$E$#.C+#%$#0s#>##nD#$##C-#%#s#A##*s#0s#-*#s#u5KGs#0nJ$E$#.C##%$#0s#*#s#BnD#$##C%#%###s#CnD#$##C4#%#(##nD#$##Cs#&#%#6##nC#$#$CH#+$#1#$#2s#F&#3#4#5s#C&#3#4#5s#C&#3#4#5s#C&#3#4#5s#C'#6#7#2#8s#)'#6#1#9#2s#)$Cs#)#j#8s$7#k#+s$<s$;k#&E#k#'E#k#(C#US0FYPRs#bs#`MKnI$s$C$#%CF#%#s#g%#)#*#nI$s$D$#+CH#%#s#p%#,#-#nL%s$Ds$D$#.Cs#y#$%#+#%#nD#$##Cs$(#%#s$###nD#$##Cs$/#%#G##nL%s$Gs$G$#.Cs#R#$%#/#%=nJ$E$#.Cs#T#%$#0s#V##nD#$##Cs$0#%#s#V##nJ$E$#.Cs#Y#%$#0s#X##nD#$##Cs#\#%#s#[##nD#$##Cs#^#%###s#?nD#$##Cs$9#%#)##nC#$#$CH#+$#1#$#2s#[&#3#4#5s#X&#3#4#5s#X&#3#4#5s#X&#3#4#5s#X'#6#7#2#8s#>'#6#1#9#2s#>$C#8j#83#k#:s$Qs$.k#;E#US=F6s$Is$9nD#$##s$2s$<#%#s$0##nI$s$W$#%CF#%#s#{%#)#*s#9nI$s$X$#+CH#%#s$(%#,#-#nL%s$Xs$X$#.C%#$%#+#%#nD#$##Cs$<#%#s$7##nD#$##Cs$C#%#G##6s#ps$@nL%s$\s$\$#.C##$%#/#%s#2nJ$E$#.Cs#i#%$#0s#k##nD#$##Cs$E#%#s#k##nJ$E$#.Cs#n#%$#0s#m##nD#$##Cs#q#%#s#p##nD#$##Cs#s#%###s#TnD#$##Cs$N#%#*##nC#$#$CH#+$#1#$#2s#p&#3#4#5s#m&#3#4#5s#m&#3#4#5s#m&#3#4#5s#m'#6#7#2#8s#S'#6#1#9#2s#S$C#s#-j#,5#UJEk#'E#k#8C#US1FnL%s$js$j$#.Cs#R#$%#+#%5nD#$##Cs$N#%#s$I##nD#$##Cs$U#%#G##6Gs$'nJ$E$#.Cs#z#%$#0s#|#s#CnD#$##Cs$V#%#s#|##nJ$E$#.C%#%$#0s#~##nD#$##Cs$&#%#s$%##nD#$##Cs$(#%###s#enD#$##Cs$_#%#)##nC#$#$CH#+$#1#$#2s$%&#3#4#5s#~&#3#4#5s#~&#3#4#5s#~&#3#4#5s#~'#6#7#2#8s#d'#6#1#9#2s#d$C#s#>j#<0#k#=ECk#>C#US>FVGMs$P%Qs$O#VMPs$J%Qs$I#nI$s%#$#%CF#%##%#)#*s#anI$s%$$#+CH#%#&%#,#-#nL%s%$s%$$#.Cs#h#$%#+#%#nD#$##Cs$d#%#s$_##nD#$##Cs$k#%#G##nJ$E$#.Cs#^#%$#0s$5#6nD#$##Cs$9#%#s$8##nD#$##Cs$;#%###s#xnD#$##Cs$r#%#&##nC#$#$CH#+$#1#$#2s$8&#3#4#5s$5&#3#4#5s$5&#3#4#5s$5&#3#4#5s$5'#6#7#2#8s#w'#6#1#9#2s#w$C#s#Qj#83#k#1Es#&k#8C#US?FnD#$##Cs$p#%#s$k#s#mnD#$##Cs$w#%#G##nJ$E$#.Cs#$#%$#0s$A#s#dnD#$##Cs$w#%#s$A##nJ$E$#.Cs#l#%$#0s$C##nD#$##Cs$G#%#s$F##6Gs$3nJ$E$#.C##%$#0s$-#s$EnD#$##Cs$2#%###s$FnD#$##Cs$L#%#&##nD#$##Cs%'#%#+##nC#$#$CH#+$#1#$#2s$I&#3#4#5s$F&#3#4#5s$F&#3#4#5s$F&#3#4#5s$F'#6#7#2#8s$,'#6#1#9#2s$,$C#s#bj#<1#k#:s%?Dk#;E#US/FnD#$##Ds%(#%#s#L#S#nD#$##C##%#s$}#s$#nD#$##Cs%-#%#G##nD#$##Cs$V#%#s$U#s#snD#$##Cs$?#%#s#o#s$SnD#$##Cs$Y#%#$##nD#$##Cs%4#%#&##nC#$#$CH#+$#1#$#2s$V&#3#4#5s$S&#3#4#5s$S&#3#4#5s$S&#3#4#5s$S'#6#7#2#8s$9'#6#1#9#2s$9$C#s#oj#$-#k#8CEUS.FUHG#s%E#nD#$##Ds%6#%#s$;#S#nD#$##C##%#s%/#s$1nD#$##C%#%#G###s$i'nD#$##C##%#s$d#s$&nD#$##Cs$g#%###1nD#$##Cs%B#%#&##nC#$#$CH#+$#1#$#2s$d&#3#4#5s$a&#3#4#5s$a&#3#4#5s$a&#3#4#5s$a'#6#7#2#8s$G'#6#1#9#2s$G$C#s#}j#?/#VS.GF#s%Q#0FUS5#US6#WS7Es%_%WS/Gs%U#*%#1Es%b((#s%X+$#2Es%e#(US9#2s%gs%gs%C*3Gs%]+nD#$##s%F.#%#$##4MKs%@%Qs%?#4PS$s%:%Qs%9#0R1Es%o#ZS0S,Ps%5#MKnI$s%r$#%CF#%#&%#)#*#nI$s%s$#+CH#%#)%#,#-#nL%s%ss%s$#.C,#$%#+#%#nD#$##C5#%#0##nD#$##C<#%#F###s%0>WS1GFs%1-S%FH5GFs%33Gs%3=-S%KGYS(S,Ps%'/KnI$s%~$#%CF#%#s$m%#)#*#nI$s&#$#/CH#%#%%#,#-#nL%s&#s&#$#.C'#$%#/#%#nJ$E$#.C)#%$#0s%2##nD#$##Cs#&#%#+##nJ$E$#.C-#%$#0s%4##nD#$##C/#%#s%7##*s$Ts#(5GFs%%nJ$E$#.C##%$#0s${#0nD#$##C%#%###1nD#$##Cs$e#%#'##nD#$##Cs$w#%#6##nC#$#$CN#+$#1#$#24&#3#4#51&#3#4#51&#3#4#51&#3#4#51'#6#7#2#8s%8'#6#1#9#2s%8VSDC#'FUS4#USEF&s#Es#Ds#8&$#US8&USFF&s#Ts#Ss#I%$#US-)USGF&s#hs#gs#Y%$#US*,USHF&s#~s#}s#m%$#US</USIF&s$5s$4s$'%$#US)2USJF&s$Ns$Ms$;%$#US:5USKF&s$ds$cs$S%$#USL8USMF&s&Ds&Cs$k%$#WS&;HNWS'FHN$C$#m#&#j#@C#YS@CCs&Qs&P#j#.C#YS@Cs&Xs&Vs&U#j#As&Z##"). Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : forall fk, mkAndB (mkbc fk) = mkAnd fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAnd); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAnd0); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.narrow_maskB); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.narrow_mask); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.narrow_maskB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAnd0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAnd0B_eqf)|] [|@b; @a; @x; @m; @k; @n; @op; @a0; @b0; @sx; @lo; @e; @i; @k'; @o; @x0; @fk|] "##`#+#@#1#%#$#'#&###8#(#=#2#4#)#>#6#9#5#0#.#/#:#;#<#*#?#@#A#B#3#7&#0&#>$#?&US$S%k#$CC$HUL#UMH$EVL#HVMEHk#%C)UPD$FVS&HS'WQ$G#US(HVDF#VEGDnK$I$#&C&#%$#'$##VGJFVFNJnC#$#$CE#+$#(%$#)&&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#WOFG+#JF*#FGDnK$I$#&C%#%$#'$###NJF#S)NJnC#$#$CE#+$#(%$#)&&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#%C*#j#/6#UKIk#1I#k#%C#UODVEG8nK$I$#&C##%$#'/#.nC#$#$CE#+$#(#$#)/&#*#+#,-&#*#+#,-&#*#+#,-&#*#+#,-'#-#.#)#/,'#-#(#0#),%C#,j#2(#WOGD=#FG<#GDEnK$I$#&C%#%$#'$###JFGnC#$#$CH#+$#($$#)%&#*#+#,#&#*#+#,#&#*#+#,#&#*#+#,#'#-#.#)#/5'#-#(#0#)5VS*C#$DUQ#US+DZR32-&$#US,&US-DZRs#-s#,9%$#WL)EHWMDEH%C$#m#&#j#3C#YS#CCs#5s#4#j#&C#YS#Cs#<s#:s#9#j#4s#>##"). Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : forall fk, mkAndKB (mkbc fk) = mkAndK fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAndK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAnd); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndB_eqf)|] [|@b; @a; @k; @n; @op0; @a0; @b1; @sx; @lo; @e; @i; @b0; @m1; @op; @op1; @a1; @b2; @i0; @z; @x; @m; @x0; @fk|] "#$3#3#M#9#%#$###&#(#,#+#*#.#/#'#)#-#D#0#C#:#<#K#1#L#>#A#@#G#?#8#6#7#I#F#E#J#2#M#N#O#=#H#B#;'#9&#J$#K%#L$US/S0k#$CC&FUS$#US%F&EVS$#FVS%EFk#%C)US)DVEGDVGHN%ES#%FS#VS*$#US+#VHG#VHKOVKIJVJPInC#$#$CH#+$#&&$#'%&#(#)#*$&#(#)#*$&#(#)#*$&#(#)#*$'#+#,#'#-#'#+#&#.#'#VNOHVOJKnC#$#/CF#+$#0%$#'$&#(#)#*#&#(#)#*#&#(#)#*#&#(#)#*#'#+#,#'#-''#+#&#.#''nQ#$#1CD#-#/#/#/#/#/#/#/#/#/##%HS#$S1US,#$$$#$#$#$#US,#%8#VS2*#VS3-#VS4S#$VS*#;US+#VIG#VILPnS&#$##C(#%#$##VLRMVMS'RnC#$#$CI#+$#&%$#'&&#2#3#4$&#2#3#4$&#2#3#4$&#2#3#4$'#+#,#'#-#'#+#&#5#'#VPMLnC#$#*CF#+$#.$$#'>&#2#3#4#&#2#3#4#&#2#3#4#&#2#3#4#'#+#,#'#-&'#+#&#.#'&nQ#$#(CD#-#@#@#@#@#@#@###@#@#@nC#$#/CE#+$#6B$#'B&#(#7#*#&#(#3#*A&#(#3#*A&#(#3#*A'#+#,#'#-@'#+#&#.#'@nC#$#)CE#+$#8#$#'?&#(#3#*>&#(#3#*>&#(#3#*>&#(#3#*>'#+#,#'#-B'#+#&#.#'BnS(#$#1CD#+###s#*#s#*#s#*#s#*#s#*#s#*#s#*nC#$#%CD#+$#6s#,$#'s#,&#1#7#/>&#1#)#/s#+&#1#)#/#&#1#)#/s#+'#+#,#'#-A'#+#&#.#'A#NGD#OHN#JGs#*#JKO#PIJ#LPInC#$#$CH#+$#&&$#'%&#(#)#*$&#(#)#*$&#(#)#*$&#(#)#*$'#+#,#'#-#'#+#&#.#'##KOH#IJKnC#$#/CF#+$#0%$#'$&#(#)#*#&#(#)#*#&#(#)#*#&#(#)#*#'#+#,#'#-''#+#&#.#''nQ#$#1CD#-#+#+#+#+#+#+#+#+#+###MG;#MLPnS&#$##C@#%#$###S'RM#S5S'RnC#$#$CI#+$#&%$#'&&#2#3#4$&#2#3#4$&#2#3#4$&#2#3#4$'#+#,#'#-#'#+#&#5#'##RMLnC#$#*CF#+$#.$$#'/&#2#3#4#&#2#3#4#&#2#3#4#&#2#3#4#'#+#,#'#-&'#+#&#.#'&nQ#$#(CD#-#1#1#1#1#1#1###1#1#1nC#$#/CE#+$#63$#'3&#(#7#*#&#(#3#*2&#(#3#*2&#(#3#*2'#+#,#'#-1'#+#&#.#'1nC#$#)CE#+$#8#$#'0&#(#3#*/&#(#3#*/&#(#3#*/&#(#3#*/'#+#,#'#-3'#+#&#.#'3nS(#$#1CD#+###7#7#7#7#7#7#7nC#$#%CD#+$#69$#'9&#1#7#//&#1#)#/8&#1#)#/#&#1#)#/8'#+#,#'#-2'#+#&#.#'2WS-C;#j#-s#H##GDE#HNG#KGs#DnC#$#$CN#+$#&#$#'8&#(#)#*7&#(#)#*7&#(#)#*7&#(#)#*7'#+#,#'#-;'#+#&#.#';nC#$#/CF#+$#0#$#'?&#(#)#*=&#(#)#*=&#(#)#*=&#(#)#*='#+#,#'#-8'#+#&#.#'8nQ#$#1CD#-#&#&#&#&#&#&#&#&#&###LGs#0nS&#$##Cs#4#%###>nC#$#$CJ#+$#&#$#'?&#2#3#43&#2#3#43&#2#3#43&#2#3#43'#+#,#'#-6'#+#&#5#'6nC#$#*CF#+$#.#$#'A&#2#3#49&#2#3#49&#2#3#49&#2#3#49'#+#,#'#-4'#+#&#.#'4nQ#$#(CD#-#>#>#>#>#>#>###>#>#>nC#$#/CE#+$#6@$#'@&#(#7#*#&#(#3#*?&#(#3#*?&#(#3#*?'#+#,#'#-s##'#+#&#.#'s##nC#$#)CE#+$#8#$#'s#'&#(#3#*s#%&#(#3#*s#%&#(#3#*s#%&#(#3#*s#%'#+#,#'#-@'#+#&#.#'@nS(#$#1CD#+###.#.#.#.#.#.#.nC#$#%CE#+$#60$#'0&#1#7#/+&#1#)#//&#1#)#/#&#1#)#//'#+#,#'#-s#)'#+#&#.#'s#)VS6C#&DUS7#US8DZS9s#\s#[6&$#WS$&EFWS%DEFWS-C$#m#&#j#9C#YS.CCs#ds#c#j#7C#YS.Cs#ks#is#h#j#:s#m##"). Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : forall fk, or_disjointB (mkbc fk) = or_disjoint fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.or_disjointB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.or_disjoint); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf)|] [|@b; @e; @p; @lo; @hi; @x; @z; @o; @x0; @fk|] "##c#*#G#1###6#$#0#%#B#9#C#2#4#7#&#(#D#:#E#5#/#-#.#;#<#@#A#?#)#'#F#G#H#I#3#>#=#8'#C$#D%#E%#F&US&S'k#$GC#DUL#UMD#FVL#DVMFDk#%GEUNHVJEE#OVR#FVS(S)FUS*S+US,#UOP$$#%D#nC#$##C(#%###InJ%EE$#&CD#$%#'#(#nK$-$#)C+#%$#&##IVQOFVNS-P$+#%D#VS#/#nJ%EE$#&CD#$%#'#(#nK$4$#)C(#%$#&##I&C*#j#*8#UK7k#%G#UQHUDFnC#$##C8#%#,#InJ%EE$#&CD#$%#'#(#nK$=$#)C%#%$#&##I&C#,j#+)#VQHDVNPS.$=#%D#VS#A#nJ%EE$#&CD#$%#'#(#nK$s#&$#)C(#%$#&##IVS/C##HUR#US0HZS$54.&$#US1&US2HZS$s#0s#/:%$#WL)FDWMHFD&C$#m#&#j#,G#YS%GCs#8s#7#j#)G#YS%Gs#?s#=s#<#j#-s#A##"). Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : forall fk, mkOrB (mkbc fk) = mkOr fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkOrB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkOr); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.or_disjoint); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.is_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zalu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_OR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndKB); constr:(@Stdlib.ZArith.BinInt.Z.lnot); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EAlu); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAndK); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.or_disjointB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.or_disjointB_eqf)|] [|@b; @a; @c; @n; @op; @a0; @b0; @sx; @lo; @e; @k; @i; @x; @y; @x0; @fk|] "#$h#/#L#5#%#C#&#$#'###:#(#)#A#*#I#=#+#,#6#8#;#>#-#J#D#9#4#2#3#@#F#G#E#.#K#L#M#N#B#7#H#?#<,#G&#H$#I&#8&#9&#5&#J$#'%#K&US,S-k#$CC$IUS##US$I$GVS##IVS$GIk#$CJk#%C#US%DUS&DWS.MGI)#*FD#EFD*DF$KVS/IS0US1#)#'&H#)I#E$#$L'#H'#E#&%MKH%MNL%MQNnC#$#%CH#+$#&&$#'%&#(#)#*$&#(#)#*$&#(#)#*$&#(#)#*$'#+#,#'#-#'#+#.#/#'#$Q'#L.#E#-%MRQ%MS'RnC#$#%CL#+$#&%$#'*&#(#)#*$&#(#)#*$&#(#)#*$&#(#)#*$'#+#,#'#-#'#+#.#/#'#$R'#N4#E#3%MS2S'nC#$#%CN#+$#&$$#'.&#(#)#*(&#(#)#*(&#(#)#*(&#(#)#*('#+#,#'#-#'#+#.#/#'#nC#$#$CD#+$#&5$#'.&#(#)#*(&#(#)#*(&#(#)#*(&#(#)#*('#+#,#'#-#'#+#.#/#'#nJ#$##C=#%#>##nJ#$##C@#%#?##nO$P$#0Cs#$#%$#1B##VIDG#EDGVIGD$H'#F@#E#?'s#%FB#E#A%MHF%MLKnC#$#%CF#+$#&%$#'$&#(#)#*#&#(#)#*#&#(#)#*#&#(#)#*#'#+#,#'#->'#+#.#/#'>$N'#Ks#(#E#s#'nC#$#%CK#+$#&#$#''&#(#)#*A&#(#)#*A&#(#)#*A&#(#)#*A'#+#,#'#-<'#+#.#/#'<nC#$#$CG#+$#&,$#''&#(#)#*#&#(#)#*#&#(#)#*#&#(#)#*#'#+#,#'#-;'#+#.#/#';nJ#$##C0#%#1##nJ#$##C3#%#2##nO$P$#0Cs#7#%$#05##(HFD(HDF&KHs#1#E#s#0&LHs#3#E#s#2nC#$#%CH#+$#&#$#'s#.&#(#)#*s#-&#(#)#*s#-&#(#)#*s#-&#(#)#*s#-'#+#,#'#-s#,'#+#.#/#'s#,&QLs#6#E#s#5nC#$#%CL#+$#&#$#'s#0&#(#)#*s#*&#(#)#*s#*&#(#)#*s#*&#(#)#*s#*'#+#,#'#-s#)'#+#.#/#'s#)&RNs#9#E#s#8nC#$#%CN#+$#&#$#'s#2&#(#)#*s#,&#(#)#*s#,&#(#)#*s#,&#(#)#*s#,'#+#,#'#-s#''#+#.#/#'s#'nC#$#$CD#+$#&,$#')&#(#)#*&&#(#)#*&&#(#)#*&&#(#)#*&'#+#,#'#-#'#+#.#/#'#nJ#$##C/#%#s#B##nJ#$##C1#%#s#C##nO$P$#0Cs#H#%$#1s#F##(FDG(FGD&HFs#B#E#s#A&KFs#D#E#s#CnC#$#%CF#+$#&#$#'s#$&#(#)#*s##&#(#)#*s##&#(#)#*s##&#(#)#*s##'#+#,#'#-s#>'#+#.#/#'s#>&NKs#G#E#s#FnC#$#%CK#+$#&#$#'s#&&#(#)#*s#@&#(#)#*s#@&#(#)#*s#@&#(#)#*s#@'#+#,#'#-s#;'#+#.#/#'s#;nC#$#$CG#+$#&)$#'&&#(#)#*#&#(#)#*#&#(#)#*#&#(#)#*#'#+#,#'#-4'#+#.#/#'4nJ#$##C,#%#s#0##nJ#$##C.#%#s#1##nO$P$#0Cs#V#%$#00##+CB#j#$s#Z#k#%Cs#cUS(DVDHs#R#E#s#QVFHs#T#E#s#SnC#$#%CH#+$#&#$#'s#O&#(#)#*s#N&#(#)#*s#N&#(#)#*s#N&#(#)#*s#N'#+#,#'#-s#M'#+#.#/#'s#MVKLs#W#E#s#VnC#$#%CL#+$#&#$#'s#Q&#(#)#*s#K&#(#)#*s#K&#(#)#*s#K&#(#)#*s#K'#+#,#'#-s#J'#+#.#/#'s#JVLNs#Z#E#s#YnC#$#%CN#+$#&#$#'s#S&#(#)#*s#M&#(#)#*s#M&#(#)#*s#M&#(#)#*s#M'#+#,#'#-s#H'#+#.#/#'s#HnC#$#$CD#+$#&,$#')&#(#)#*&&#(#)#*&&#(#)#*&&#(#)#*&'#+#,#'#-#'#+#.#/#'#nJ#$##Cs#0#%#s#c##nJ#$##Cs#2#%#s#d##nO$P$#0Cs#i#%$#1s#g##*Fs#a#E#s#`VDFs#c#E#s#bnC#$#%CF#+$#&#$#'s#C&#(#)#*s#B&#(#)#*s#B&#(#)#*s#B&#(#)#*s#B'#+#,#'#-s#]'#+#.#/#'s#]VHKs#f#E#s#enC#$#%CK#+$#&#$#'s#E&#(#)#*s#_&#(#)#*s#_&#(#)#*s#_&#(#)#*s#_'#+#,#'#-s#Z'#+#.#/#'s#ZnC#$#$CG#+$#&)$#'&&#(#)#*#&#(#)#*#&#(#)#*#&#(#)#*#'#+#,#'#-2'#+#.#/#'2nJ#$##Cs#+#%#s#O##nJ#$##Cs#-#%#s#P##nO$P$#0Cs#u#%$#0.##+C#Bj#-@#US&GnO$P$#0C##%$#1s#w#s#&(DGI#EGI(DIG&FDs#t#E#s#s&HDs#v#E#s#u%MFDnC#$#%CD#+$#&$$#'#&#(#)#*s#r&#(#)#*s#r&#(#)#*s#r&#(#)#*s#r'#+#,#'#-s#V'#+#.#/#'s#VnC#$#$CI#+$#&'$#'#&#(#)#*s#G&#(#)#*s#G&#(#)#*s#G&#(#)#*s#G'#+#,#'#-s#3'#+#.#/#'s#3nJ#$##C*#%#+##nJ#$##C-#%#,##nO$P$#0C0#%$#0/##VS3C#$DUS)#US4DZS*s#4s#36&$#US5&US6DZS*s$4s$3s#8%$#WS#)GIWS$DGI+C$#m#&#j#2C#YS+CCs$=s$<#j#0C#YS+Cs$Ds$Bs$A#j#3s$F##"). Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma conc_tryB_eqf : forall fk, conc_tryB (mkbc fk) = conc_try fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.conc_tryB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.conc_try); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.closedb); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.evalS_def); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.conc_limit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.evalS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.wrap64); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.probeS); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.all_eval_toS); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@cands; @x; @v; @p; @lo; @hi; @o; @e; @IH; @rest; @s; @fk|] "#$>#.#V###I#6#%#$#&#'#(#5#4#)#+#*#,#B#7#9#V#1#<#?#A#@#C#E#G#Q#O#M#R#K#S#>#3#2#=#D#F#H#J#P#N#T#U#-#W#X#:#8#;#L(#3&#S$#T&#2&#U'US%S5US%LUKEk#$$#$CUR#US#C$GVR#CVS#GC$H&#FC#HFC%-$#j#$/#US6L#FG#VS&1#$I&#HC#IHC%5$##JIGUS'HVS(HJUS)#VQEE$MVS*#HVS+CGVS7#S8US9GWS,M#NVS:GF'OPCGVS+GFUS;S-US.#VS<%#VS/F#'OPC#nD#$##D)#%###S0nD#$##D+#%#S1##US.S-VS/+#US=#YS2OPCF#VS>ECnD#$##s#0$#%###InD#$##s#1)#%###InK$E$#%s#24#%$#&##HnD#$##s#37#%###HnQ%EE$#'s#4C#$%#(#)#nK$=$#%s#5;#%$#'##CnD#$##s#6?#%#C##nD#$##s#7B#%#C###MJFVS$MH#S?PMnD#$##s#;/#%#.##nD#$##s#<4#%###$#PNJnK$E$#%s#>@#%$#&$##nD#$##s#?s###%###$nQ%EE$#'s#@C#$%#(#)#nK$s#)$#%s#A*#%$#'##+nD#$##s#Bs#+#%#,##nD#$##s#Cs#.#%#-##%s#D/#j#*s#E#UKs#.k#+L#US$JUCHnK$s#2$#%s#J##%$#',#4nD#$##s#Ks#4#%#5##nD#$##s#Ls#7#%#6##%s#M#,j#*)#US'FVS(FIUS)#VS$JFWS,Js#6O'MNCG'MNCs#0nD#$##D$#%###S0nD#$##Ds#8#%#S1##YS2MNCFs#-nD#$##s#Y##%#s#,#>nD#$##s#Z%#%###?#NOInK$E$#%s#\+#%$#&$##nD#$##s#]s#A#%###$nQ%EE$#'s#^C#$%#(#)#nK$s#G$#%s#_/#%$#'##s#KnD#$##s#`1#%#s#L##nD#$##s#a4#%#s#M##VS&s#b#$JUS*#US@JZS3A@:&$#&&IGZS3s#hs#Ts#%$#CWSALFG&)I##JI$%s#l$#m#'#j#,s#[#j#-s#p#j#.L#YSBLs#es#b#Cj#$s#s#YS4s#ts#ss#ms#l#j#+L#YS4Ls#ts#rs#q#j#/s#x##"). Qed.
#[export] Hint Rewrite conc_tryB_eqf : bceq.
Lemma concretizeB_eqf : forall fk, concretizeB (mkbc fk) = concretize fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.concretize); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.conc_try); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.closedb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.eval_closed); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.nubE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.subexprs); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.conc_tryB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.conc_tryB_eqf)|] [|@cands; @e; @o; @x; @fk|] "##H#&#:#$###,#3#9#)#0#/#1#5#6#8#7#4#*#-#.#%#:#;#<#2#+#UHQURS#UIDUJ#UKDUHEk#$#'k#%E#UFCULCUMCUNCUO#VDC#nG#$##/'#%#&##WFS$C%nG#$##1)#%#(##WP2%#j#&-#ULDUMDUNDUO#WFCD#nG#$##9'#%#&##VS%:#UICUS&#US'CZS(87-&$#VJ&DVKCDWPA$#m#&#j#'E#YS)Es#$BA#j#(s#&##"). Qed.
#[export] Hint Rewrite concretizeB_eqf : bceq.
Lemma foldKB_eqf : forall fk, foldKB (mkbc fk) = foldK fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.foldKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.foldK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.concretize); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB_eqf)|] [|@e; @x; @v; @p; @lo; @hi; @z; @n; @op; @a; @b; @sx; @e0; @k; @i; @o; @fk|] "#$,#-#C#3#9#8#$###%#<#'#(#@#&#)#*#+#4#6#:#?#A#=#7#0#1#>#,#B#C#D#E#2#5#;(#3%#A$#5%#6%#B&US(S)$GUQ#URGUEDk#$C#US#FVIDD$M&#HVS*FGUS$FUJKUS$GnE$D$#%C$#%$#&##KnL#$##C'#%#&##nI%DD$#'CG#$%#(#)#UFHnE$D$#%C##%$#&'#HnE$.$#%C,#%$#'%##$K&#JUNOnE$D$#%C##%$#&,#OnL#$##C0#%#/##nI%DD$#'CG#$%#(#)#UMJnE$D$#%C##%$#&0#JnE$7$#%C)#%$#'%##$N&#KUOPnE$D$#%C##%$#&5#PnL#$##C9#%#8##nI%DD$#'CG#$%#(#)#nE$>$#%C'#%$#'##7nC#$#$CF#+$#*H$#+3&#,#-#.*&#,#-#.*&#,#-#.*&#,#-#.*'#/#(#+#0#'#/#1#2#+#%MH#NKnE$D$#%C##%$#&<#KnL#$##C@#%#?##nI%DD$#'CG#$%#(#)##MHnE$D$#%C##%$#&@#HnE$s#'$#%C)#%$#'%##%KJ#POnE$D$#%C##%$#&s#$#OnL#$##Cs#(#%#s#'##nI%DD$#'CG#$%#(#)##KJnE$D$#%C##%$#&s#(#JnE$s#/$#%C)#%$#'%##%NK#S+PnE$D$#%C##%$#&s#,#PnL#$##Cs#0#%#s#/##nI%DD$#'CG#$%#(#)#nE$s#5$#%C'#%$#'##5nC#$#$CF#+$#*H$#+1&#,#-#.)&#,#-#.)&#,#-#.)&#,#-#.)'#/#(#+#0#'#/#1#2#+#'C:#j#3s#:#UEs#9k#$C#US%FnE$s#<$#%Cs#2#%$#':#8nE$s#=$#%Cs#*#%$#'3#1nE$s#>$#%Cs#9#%$#',#>nC#$#$CF#+$#*H$#+%&#,#-#.$&#,#-#.$&#,#-#.$&#,#-#.$'#/#(#+#0#'#/#1#2#+#'C#,j#3)#%HFnL#$##Cs#@#%#s#?#7nI%DD$#'CG#$%#(#)##HFnE$D$#%C##%$#&s#@#FnE$s#G$#%C'#%$#'%##%JM#ONnE$D$#%C##%$#&s#D#NnL#$##Cs#H#%#s#G##nI%DD$#'CG#$%#(#)##JMnE$D$#%C##%$#&s#H#MnE$s#O$#%C)#%$#'%##nC#$#$CG#+$#*F$#++&#,#-#.#&#,#-#.#&#,#-#.#&#,#-#.#'#/#(#+#0s##'#/#1#2#+s##VS,C#$FUS&#US-FZS'=<6&$#US.&US/FZS's#Zs#YB%$#VQ)GVRFG'C$#m#&#j#%C#YS0CCs#cs#b#j#4s#f##"). Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
Lemma lin_branchB_eqf : forall fk, lin_branchB (mkbc fk) = lin_branch fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.branch_cond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_branchB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_branch); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.option_map); constr:(@Corelib.Init.Datatypes.negb); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf)|] [|@b; @a; @neg; @pos; @c; @p0; @z0; @bh; @x; @p; @z; @ah; @e; @o; @x1; @x0; @fk|] "#$z#.#V#7#A###5#&#I#G#4#%#6#@#$#'#F#R#)#8#:#*#,#D#K#<#=#N#L#+#S#-#T#;#1#2#C#E#J#O#M#U#V#W#X#Y#B#?#9#H#Q#P#>#3.#:&#N'#O&#P$#Q%#R'#S$#%%#@%#T&#U(US2S3ULCk#$F#k#%F#&EUS##US$E&NVS##EVS$NE&KWS##NEWS$KNEk#&S)Ck#'S)#US*GVMFDUS4S'$FDN#US5%%&$#$FDKP%(#%*%#$FDK)%+#($FDNP%-#**%#nC#$##C(#%#I##nJ#$#(CG#)#H#I#I#I#I#I'C#*,'*(-nC#$##C$#%###HnJ#$#(CG#)#I#H#H#H#H#H'C#US6CnC#$##s#'&#%#$##nC#$##s#(,#%#*##VMDD&OVS(#K&S%VS(#OUS7S'US+#)S')#)#)#)#US+#VS8)#VS,G#VS,E$nC#$##C$#%###H$FDS%s#*%s#,#s#)$FDS-P%s#.#s#+VR%#'CI$FDS%P%s#2#s#/VR'#'CHnC#$##s#D$#%###@nC#$##s#E)#%#(##(CCQ#nJ#$#(s#GS&#)#####$######nC#$##s#H1#%###s#$nM%DD$#)s#IE#$%#*#+#nL$s##$#,s#J?#%$#)##s#&nM%DD$#-s#KE#$%#.#/#nL$s#%$#,s#Ls###%$#-##s#(nC#$##s#Ms#.#%#,#s#)nC#$##s#Ns#8#%#1##(CCQ#nJ#$#(s#PG#)#s#*#s#*#&#&#$###Os#>s#<#Os#:s#8VS.$##Os#?s#:#Os#;s#@nC#$##C$#%###HnC#$##s#W##%#s#4#s#3nC#$##s#X'#%#s#:##+OK+S%OVS9s#&s#%#S/s##A#S/B>nC#$##s#^##%#=#s#:nC#$##s#_%#%#B##(CCQ#nJ#$#(s#aS&#)#####$######nC#$##s#b)#%###s#>nM%DD$#)s#cE#$%#*#+#nL$s#=$#,s#d,#%$#)##s#@nM%DD$#-s#eE#$%#.#/#nL$s#?$#,s#f/#%$#-##s#BnC#$##s#g5#%#s#&#s#CnC#$##s#h9#%#s#+##(CCQ#nJ#$#(s#jG#)#4#4#&#&#$##,s#k=#j#$s#_#ULs#Fk#0F#US0GnC#$##CA#%#I#@nC#$##s#q##%#s#S#<UEKUGOnC#$##s#ts#=#%#5#s#PnM%DD$#)s#uE#$%#*#+#nL$s#O$#,s#v%#%$#)##s#RnM%DD$#-s#wE#$%#.#/#nL$s#Q$#,s#x(#%$#-##s#TnJ#$#(s#yG#)#*#*#####3#2,s#z#2j#1/#$FDEs#l%s#n#s#k#G#s#d$FDEP%s#q#s#n#Gs#n#VS.&#nJ#$#(CK#)#H#I#I#I#I#I'C##Gs#k'#G(s#lnC#$##C$#%###HnJ#$#(CK#)#I#H#H#H#H#H'C#nC#$##s$.%#%###s#fnC#$##s$/+#%#)##+GN+RG$FDRs#~%s$$#s#}#S&#s#Q$FDRP%s$'#s$$#S&s#T#nC#$##s$8##%#s#S#s#pnC#$##s$9'#%#s#X##(CCQ#nJ#$#(s$;S-#)#####$######nC#$##s$<s#?#%###s#tnM%DD$#)s$=E#$%#*#+#nL$s#s$#,s$>/#%$#)##s#vnM%DD$#-s$?E#$%#.#/#nL$s#u$#,s$@2#%$#-##s#xnC#$##s$A:#%#s#\#s#ynC#$##s$BB#%#s#a##(CCQ#nJ#$#(s$DK#)#7#7#&#&#$##VS:s$E#&GUS(#US;GZS1s#9s#8s#,&$#US<&US=GZS1s$?s$>s#>%$#XS#)KNEXS$GKNE,s$O$#m#&#j#2F#-Fs$Rs$Hs$G#j#3F#-Fs$Ss$Ms$L#j#,J#-Js$Ts$Rs$Q#j#4s$X##"). Qed.
#[export] Hint Rewrite lin_branchB_eqf : bceq.
Lemma decide_branchB_eqf : forall fk, decide_branchB (mkbc fk) = decide_branch fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.branch_cond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.decide_branchB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.decide_branch); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_branch); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lit_branch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.cond_on_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.diff_branch); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.range_branch); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_branchB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_branchB_eqf)|] [|@b; @a; @c; @p0; @bl; @bh; @x; @p; @al; @ah; @t; @y; @n; @op; @a0; @b0; @sx; @lo; @e; @k; @i; @o; @x1; @x0; @fk|] "#%Z#2#N#:#;#H###&#'#(#G#)#$#%#*#9#+#,#<#>#8#.#/#-#@#C#L#I#?#5#6#K#0#1#M#N#O#P#=#B#D#E#F#J#A#7.#F$#:%#;%#G%#H%#I$#J&#K(#8'#L&#M(US-S.UCDk#$O#k#%O##FUR#US#F#LVR#FVS#LF#MWR#LFWS#MLFk#&S$,US(GWS)ILF&D#'HG(I&D#)IHG&DFVJEE#K%#H#Q%#K*S%HGLFnJ%EE$#'=F#$%#(#)#US/DnC$*$#*?&#%$#'$##nJ%EE$#+@F#$%#,#-#nC$,$#*A*#%$#+##%WMIHGnC$D$#*s##$#%$#./##nC$D$#*s#$1#%$#.0##nD#$##s#%5#%#3##'KI(N&D#)NKI#P%#K#S%%#P*S0HGLFnJ%EE$#'s#/F#$%#(#)#nC$;$#*s#0%#%$#'##4nJ%EE$#+s#1F#$%#,#-#nC$=$#*s#2)#%$#+##6WHNKInC$D$#*s#4$#%$#.@##nC$D$#*s#5.#%$#.A##nD#$##s#62#%#0##'NK(P&D#)PNK%s##N#S&%#Q*S1HGLFnJ%EE$#'s#?F#$%#(#)#nC$s#+$#*s#@%#%$#'##s#$nJ%EE$#+s#AF#$%#,#-#nC$s#-$#*s#B)#%$#+##s#&WIPNKnC$D$#*s#D$#%$#.s#0##nC$D$#*s#E-#%$#.s#1##nD#$##s#F1#%#/##nO#$#$s#GM#+$#/s#8$#0s#$&#1#2#33&#1#2#33&#1#2#33&#1#2#33'#4#5#0#6#'#4#7#8#0#'GM(H&D#)HGM#I%#G%s#&I*S'HGLFnJ%EE$#'s#PF#$%#(#)#nC$s#<$#*s#Q%#%$#'##s#5nJ%EE$#+s#RF#$%#,#-#nC$s#>$#*s#S(#%$#+##s#7WLHGMnC$D$#*s#U$#%$#.s#A##nC$D$#*s#V-#%$#.s#B##nD#$##s#W1#%#/##'IH(K&D#)KIH#N%#I#S'%#N*S&HGLFnJ%EE$#'s#aF#$%#(#)#nC$s#M$#*s#b%#%$#'##s#FnJ%EE$#+s#cF#$%#,#-#nC$s#O$#*s#d)#%$#+##s#HWGKIHnC$D$#*s#f$#%$#.s#R##nC$D$#*s#g.#%$#.s#S##nD#$##s#h2#%#0##nO#$#%s#iM#+$#*s#$$#04&#1#2#3#&#1#2#3#&#1#2#3#&#1#2#3#'#4#5#0#6s#5'#4#7#8#0s#5$KH$QKnC$s#W$#*s#l##%$#'s#Q#s#PnJ%EE$#+s#mF#$%#,#-#nC$s#Y$#*s#n&#%$#+##s#R+KIHGnC$D$#*s#p$#%$#.s#\##nC$D$#*s#qs#^#%$#.s#]##nD#$##s#rs#b#%#s#`##$PK$S%PnC$s#`$#*s#u##%$#'s#H#s#YnJ%EE$#+s#vF#$%#,#-#nC$s#b$#*s#w&#%$#+##s#[+PNKInC$D$#*s#y$#%$#.s#e##nC$D$#*s#zs#S#%$#.s#f##nD#$##s#{s#W#%#s#U##$QN$S&QnC$s#i$#*s#~##%$#'s#A#s#bnJ%EE$#+s$#F#$%#,#-#nC$s#k$#*s$$&#%$#+##s#d+QPNKnC$D$#*s$&$#%$#.s#n##nC$D$#*s$'s#K#%$#.s#o##nD#$##s$(s#O#%#s#M##nO#$#$s$)M#+$#/s#v$#05&#1#2#3,&#1#2#3,&#1#2#3,&#1#2#3,'#4#5#0#6#'#4#7#8#0#$IG$PInC$s#s$#*s$,##%$#'s#:#s#lnJ%EE$#+s$-F#$%#,#-#nC$s#u$#*s$.&#%$#+##s#n+IHGMnC$D$#*s$0$#%$#.s#x##nC$D$#*s$1s#D#%$#.s#y##nD#$##s$2s#H#%#s#F##$NI$S'NnC$s#|$#*s$5##%$#'s#2#s#unJ%EE$#+s$6F#$%#,#-#nC$s#~$#*s$7&#%$#+##s#w+NKIHnC$D$#*s$9$#%$#.s$%##nC$D$#*s$:s#=#%$#.s$&##nD#$##s$;s#A#%#s#?##nO#$#%s$<M#+$#*5$#0,&#1#2#3#&#1#2#3#&#1#2#3#&#1#2#3#'#4#5#0#6?'#4#7#8#0?,s$=s#2#j#9s$2#UCs$*k#6O#US*GUMHUIKnC$s$/$#*s$D##%$#'s$)#s$(nJ%EE$#+s$EF#$%#,#-#nC$s$1$#*s$F&#%$#+##s$*nC$D$#*s$G##%$#.s$3#s#6nC$D$#*s$Hs$5#%$#.s$4##nD#$##s$Is$9#%#s$7##UHKUNPnC$s$7$#*s$L##%$#'s#{#s$0nJ%EE$#+s$MF#$%#,#-#nC$s$9$#*s$N&#%$#+##s$2nC$D$#*s$O##%$#.s$;#s#5nC$D$#*s$Ps$)#%$#.s$<##nD#$##s$Qs$-#%#s$+##UINUPQnC$s$?$#*s$T##%$#'s#s#s$8nJ%EE$#+s$UF#$%#,#-#nC$s$A$#*s$V&#%$#+##s$:nC$D$#*s$W##%$#.s$C#s#4nC$D$#*s$Xs#|#%$#.s$D##nD#$##s$Ys$$#%#s#~##nO#$#$s$ZM#+$#/s$K$#03&#1#2#3+&#1#2#3+&#1#2#3+&#1#2#3+'#4#5#0#6#'#4#7#8#0#ULGUHInC$s$H$#*s$]##%$#'s#k#s$AnJ%EE$#+s$^F#$%#,#-#nC$s$J$#*s$_&#%$#+##s$CnC$D$#*s$`##%$#.s$L#s#3nC$D$#*s$as#t#%$#.s$M##nD#$##s$bs#x#%#s#v##UGIUKNnC$s$P$#*s$e##%$#'s#b#s$InJ%EE$#+s$fF#$%#,#-#nC$s$R$#*s$g&#%$#+##s$KnC$D$#*s$h##%$#.s$T#s#2nC$D$#*s$is#l#%$#.s$U##nD#$##s$js#p#%#s#n##nO#$#%s$kM#+$#*3$#0+&#1#2#3#&#1#2#3#&#1#2#3#&#1#2#3#'#4#5#0#6<'#4#7#8#0<,s$l#s#2j#9s#/#WS)HLF&D#nO#$#$s$pL#+$#/#$#0s#@&#1#2#3s#7&#1#2#3s#7&#1#2#3s#7&#1#2#3s#7'#4#5#0#6s#S'#4#7#8#0s#S'ML(G&D#)GML$HM$NH*QHGLFnJ%EE$#'s$xF#$%#(#)#nC$s$d$#*s$y%#%$#'##s$]nJ%EE$#+s$zF#$%#,#-#nC$s$f$#*s${(#%$#+##s$_+HGMLnC$D$#*s$}$#%$#.s$i##nC$D$#*s$~,#%$#.s$j##nD#$##s%#0#%#.##nO#$#%s%$L#+$#*2$#0#&#1#2#3s#l&#1#2#3s#l&#1#2#3s#l&#1#2#3s#l'#4#5#0#6s#G'#4#7#8#0s#GVS2s%%##GUS+#US3GZS,s#Gs#F:&$#US4&US5GZS,s$|s${s#L%$#XR)MLFXS#GMLF,s%/$#m#&#j#:O#-Os%2s%(s%'#j#;O#-Os%3s%-s%,#j#*S$#-S$s%4s%2s%1#j#<s%8##"). Qed.
#[export] Hint Rewrite decide_branchB_eqf : bceq.
Lemma mkSltB_eqf : forall fk, mkSltB (mkbc fk) = mkSlt fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.branch_cond); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSltB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkSlt); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.decide_branch); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.decide_branchB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.decide_branchB_eqf)|] [|@b; @a; @op; @c; @b0; @x; @z0; @n; @op0; @a0; @sx; @lo; @e; @k; @i; @z; @o; @x2; @x1; @x0; @fk|] "##r#.#D#6#%#$#<#'#&#;###(#)#*#7#9#+#5#4#,#=#@#>#1#2#A#B#C#-#D#E#F#:#?#8#3'#A&#4'#B$#C(US'S(k#$CCk#%C#k#&Q#%JUN#UOJ%EVN#JVOEJ%DWN#EJWODEJ%HXN#DEJXOHDEJUIFk#$C#k#%C#k#'R#US$G#KGHWDLGHUS)S*US%#US%S+nF#$#(CJ#%#$##nI$F$#)C'#%$#(##(WGPLK#MLKnI$F$#)C$#%$#(&##WKS#ML#PMLnI$F$#)C$#%$#()##nC#$#$CD#+$#*/$#+)&#,#-#(&&#,#-#(&&#,#-#(&&#,#-#(&'#.#/#+#0#'#.#1#2#+#WEKHD#GHDnI$F$#)C$#%$#(-##WHMKG#LKGnI$F$#)C$#%$#(0##nC#$#%CD#+$#3)$#+&&#,#-#(#&#,#-#(#&#,#-#(#&#,#-#(#'#.#/#+#0-'#.#1#2#+-$MLGHnI$F$#)C##%$#(3#8$S#PLKnI$F$#)C##%$#(5#2$S,S#MLnI$F$#)C##%$#(7#1nC#$#$CD#+$#*=$#+'&#,#-#(%&#,#-#(%&#,#-#(%&#,#-#(%'#.#/#+#0#'#.#1#2#+#$LKHDnI$F$#)C##%$#(:#0$PMKGnI$F$#)C##%$#(<#/nC#$#%CD#+$#3'$#+%&#,#-#(#&#,#-#(#&#,#-#(#&#,#-#(#'#.#/#+#0*'#.#1#2#+*WS&C/#j#4s#&#nC#$#$CE#+$#*6$#+(&#,#-#(&&#,#-#(&&#,#-#(&&#,#-#(&'#.#/#+#0-'#.#1#2#+-$KGDE#HDEnI$F$#)C$#%$#(s####nC#$#%CE#+$#3&$#+#&#,#-#(3&#,#-#(3&#,#-#(3&#,#-#(3'#.#/#+#0*'#.#1#2#+*VS-C#%GUS.#US/GZS0s#0s#/,&$#YN&HDEJYOGHDEJWS&C$#m#&#j#5C#&CCs#;s#:#j#6C#&Cs#Js#@s#?#j#7Q#&Qs#Ks#Es#D#j#)R#&Rs#Ls#Js#I#j#8s#P##"). Qed.
#[export] Hint Rewrite mkSltB_eqf : bceq.
Lemma mkAluK0B_eqf : forall fk, mkAluK0B (mkbc fk) = mkAluK0 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluK0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluK0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.Riscv.Instr.branch_cond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkSlt); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.BC_LT); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SLT); constr:(@LinuxProcessSemantics.Riscv.Instr.BC_LTU); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SLTU); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.is_lit); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SUB); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.shamt_of); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSrlB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkOrB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkSrl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkOr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAnd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAndK); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSrlB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAndKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkOrB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSltB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSltB_eqf)|] [|@b; @a; @op; @c; @k; @n; @op0; @a0; @b0; @sx; @lo; @e; @i; @x; @z; @s; @z0; @x1; @x0; @fk|] "#$l#-#^#4#&#%#$###'#(#)#D#3#N#M#*#5#7#=#>#?#@#+#V#W#X#:#A#B#E#H#J#K#L#O#R#S#T#,#Y#U#0#1#9#C#G#I#F#Q#P#Z#[#\#]#^#_#`#6#<#;#8#2+#Y$#G&#Z&#H&#[&#\)#:(#](US9S:k#$CCk#%C##GUP#UQG#FVP#GVQFG#EWP#FGWQEFGk#&L,k#'S;#US*D%DEFXGRS#EFXGS$S%EFVS+EFUS,S<US-E%HDEVS=GS.US/S0VS>S.#VS?%#US,$%S1#DnN#$##C%#%###)%JIH%OJInC#$#$CF#+$#(%$#),&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#nM$K$#1C.#%$#2-##nN#$##C1#%#0##US@S0USA#US/#VS2F##IWS3#DGnM$K$#1C%#%$#3##;nM$K$#1C7#%$#26###HWS4#EFnN#$##C<#%#E###JWS5#HD&$DH#S&&#IJ#S6&#JOnC#$#$CE#+$#4($#)'&#*#+#,%&#*#+#,%&#*#+#,%&#*#+#,%'#-#.#)#/#'#-#(#0#)#&1DE#O&#IH&*JInC#$#%CE#+$#2'$#)&&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#nL#$#&CD#-#s#-#s#-#s#-#s#,#s#+#;#3#s#-#0##)HRS#EF)HS$S%EFWS'IDGnM$K$#1C;#%$#3##s#1nM$K$#1Cs#-#%$#2s#,##WS(HEFnN#$##Cs#1#%#E##WS)JHD$JDH$S&IJ$S6JOnC#$#$CE#+$#4&$#)%&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#$IDE$OIH$S&JInC#$#%CE#+$#2&$#)%&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#nL#$#&CD#-#s#>#s#>#s#>#2#1#s#,#.#s#>#,##'C4#j#/s#B#US(DVGEFnN#$##Cs#@#%#E##nL#$#&CD#-#s#D#s#D#s#D#8#7#s#2#s#*#s#D###:'C#)j#/s#S#US7DVEDHVHIJVIJOnC#$#$CE#+$#4s#,$#)%&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#VFDEVDIHVHJInC#$#%CE#+$#2&$#)%&#*#+#,$&#*#+#,$&#*#+#,$&#*#+#,$'#-#.#)#/#'#-#(#0#)#nL#$#&CD#-#s#P#s#P#s#P#s#$#s###s#>#s#6#s#P#>##'C#5j#/s#_#US)DVEHDnC#$#$CE#+$#4#$#)A&#*#+#,@&#*#+#,@&#*#+#,@&#*#+#,@'#-#.#)#/?'#-#(#0#)?nC#$#%CE#+$#2#$#)>&#*#+#,=&#*#+#,=&#*#+#,=&#*#+#,='#-#.#)#/<'#-#(#0#)<nL#$#&CD#-#s#W#s#W#s#W#s#+#s#*#s#E#s#=#s#W#s#%##'C#<j#/s#f#k#3KCk#%C#US'DVFDGnM$K$#1Cs#H#%$#3##s#^nM$K$#1Cs#Z#%$#2s#Y##nL#$#&CD#-#s#`#s#`#s#`#s#4#s#3#s#N###s#`#s#.#s#%'C#s#%j#/)#%EFG)DRS#FG)DS$S%FGVS+FGUS-F%S1s#]EnN#$##Cs#_#%###s#i%IHDnC#$#$CG#+$#($$#)s#k&#*#+#,#&#*#+#,#&#*#+#,#&#*#+#,#'#-#.#)#/s#]'#-#(#0#)s#]nM$K$#1C'#%$#2s#l##nN#$##C)#%#s#i##VS2Gs#YWS'HEGnM$K$#1C$#%$#3##/nM$K$#1C,#%$#2s#q##WS(DFGnN#$##C/#%#F##WS)IDE$IED$OHInC#$#$CF#+$#4%$#)$&#*#+#,#&#*#+#,#&#*#+#,#&#*#+#,#'#-#.#)#/s#B'#-#(#0#)s#B$HEF$JHDnC#$#%CF#+$#2%$#)$&#*#+#,#&#*#+#,#&#*#+#,#&#*#+#,#'#-#.#)#/s#A'#-#(#0#)s#AnL#$#&CE#-#:#:#:#9#8#0#,#:#*##VSBC##DUS3#USCD(s#'s#&@&$#US5&USDD(s$4s#2s#,%$#US8)USED(s$7s#As#6%$#US4,USFD(s$:s#Js#E%$#USG/USHD(s$2s$1s#N%$#XP2EFGXQDEFG'C$#m#&#j#5C#*CCs$;s$:#j#6C#*Cs$Fs$@s$?#j#1L#*Ls$Gs$Es$D#j#7s$J##"). Qed.
#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Lemma mkAluKB_eqf : forall fk, mkAluKB (mkbc fk) = mkAluK fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluK0); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.foldKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.foldK); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.foldKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluK0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluK0B_eqf)|] [|@b; @a; @op; @e; @x1; @x0; @x; @fk|] "##R#(#9#/###&#$#%#0#2#.#4#'#7#6#3#+#,#8#9#:#;#1#5#-&#6$#7&#8(UPQk#$CCk#%C##DUH#UID#FVH#DVIFD#GWH#FDWIGFDk#&J,UKE#LWDEGFVN$#XKLEGFVML#$C%#j#'*#k#'CCUMEUD($C#(j#'&#XKEGFDVME#VRC##EUN#US#EZO-,)&$#US$&US%EZO981%$#XH)GFDXIEGFD$C$#m#&#j#(C#%CCA@#j#)C#%Cs#,s#&s#%#j#*J#%Js#-s#+s#*#j#+s#0##"). Qed.
#[export] Hint Rewrite mkAluKB_eqf : bceq.
Lemma mkMdKB_eqf : forall fk, mkMdKB (mkbc fk) = mkMdK fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkMdKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkMdK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluK); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.is_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkMd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.pow2_log); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SRL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_AND); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluKB_eqf)|] [|@b; @a; @op; @x; @k; @m; @n; @op0; @a0; @b0; @sx; @lo; @e; @i; @z; @x1; @x0; @fk|] "##k#+#G#2###$#%#&#@#:#'#(#1#3#5#)#>#A#8#;#?#F#D#9#.#/#7#=#*#E#C#B#G#H#I#6#<#4#0'#D&#E$#2'#F(US(S)k#$CCk#%C#$DUM#UND$EVM#DVNED$FWM#EDWNFEDk#&S*,URGUS#F#JGF#GFEUS+DUS$DWFPJ#nH$I$#'C%#%$#(##'#OKJ#S,OKnC#$#$CE#+$#)%$#**&#+#,#-$&#+#,#-$&#+#,#-$&#+#,#-$'#.#/#*#0#'#.#(#1#*#US-S%US&#VS.#DUS&S%VS/$#US$#WFQJ#nH$I$#'C0#%$#(##2nC#$#$CE#+$#)#$#*3&#+#,#--&#+#,#--&#+#,#--&#+#,#--'#.#/#*#0,'#.#(#1#*,nL#$#&CG#+#3#3#3#3#3#,#3##nH$I$#'C6#%$#25##%OPJ3nH$I$#'C5#%$#(##7nC#$#$CE#+$#)#$#*8&#+#,#-2&#+#,#-2&#+#,#-2&#+#,#-2'#.#/#*#01'#.#(#1#*1%OQJ+nH$I$#'C8#%$#(##:nC#$#$CE#+$#)#$#*;&#+#,#-5&#+#,#-5&#+#,#-5&#+#,#-5'#.#/#*#04'#.#(#1#*4nL#$#&CG#+#;#;#;#;#;#&#;##nH$I$#'C>#%$#2=##WS'C+#j#0B#US#E#FED%KPG?nH$I$#'CA#%$#(##B#KJGnC#$#$CD#+$#)$$#*s#$&#+#,#-#&#+#,#-#&#+#,#-#&#+#,#-#'#.#/#*#0?'#.#(#1#*?%KQG8nH$I$#'Cs#%#%$#(##s#&nC#$#$CD#+$#)#$#*s#'&#+#,#-&&#+#,#-&&#+#,#-&&#+#,#-&'#.#/#*#0B'#.#(#1#*BnL#$#&CF#+#*#*#*#*#*#&#*##nH$I$#'C,#%$#2s#)##VS0C#$GUS1#US2GZS3s#2s#12&$#XM&FEDXNGFEDWS'C$#m#&#j#3C#&CCs#:s#9#j#4C#&Cs#Es#?s#>#j#'L#&Ls#Fs#Ds#C#j#5s#I##"). Qed.
#[export] Hint Rewrite mkMdKB_eqf : bceq.
Lemma zband32B_eqf : forall fk, zband32B (mkbc fk) = zband32 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.zband32B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zband32); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_range); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_of); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.opp); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf)|] [|@e; @p; @lo; @hi; @x; @o; @fk|] "##W#&#D#4#-###$#3#2#,#B#)#/#.#0#5#9#8#:#@#>#;#6#*#?#=#<#%#C#D#E#F#1#+#A#7%#B$#C&UKS'ULEUM#UNEVGCCUH#k#$I#UOFVGCIUK#UPFWQC$#WRC%$$E$#US(S#US$##S#######US$#VS)(#US*#VS%#FVS%E%nD#$##D$#%###JnG%CC$#%DE#$%#&#'#nH$9$#(D0#%$#%##JUOS+$#43VS,)(nG%CC$#%DE#$%#&#'#nH$>$#(D%#%$#%##JWS&D(#j#)>#UPEWQC=#WRC>$$A$#nH$s#%$#(D##%$#%*#JVS-D#ULFUS.#US/FZS0s#(s#',&$#VM&EVNFEWS&D$#m#&#j#(I#YS1IDs#2s#1#j#*s#5##"). Qed.
#[export] Hint Rewrite zband32B_eqf : bceq.
Lemma mkAluwK0B_eqf : forall fk, mkAluwK0B (mkbc fk) = mkAluwK0 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwK0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluwK0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zband32); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.is_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zsx32); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sx32_stable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluw); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.zband32B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.zband32B_eqf)|] [|@b; @a; @d; @p; @lo; @hi; @x; @v; @op; @e; @o; @x1; @x0; @fk|] "##{#+#F#2###&#:#$#7#%#C#'#1#3#5#?#(#)#D#8#;#@#6#.#/#>#=#A#*#E#F#G#H#4#<#B#9#0)#A$#B&#C&#3%#D&#E(US'S(k#$CCk#%C##DUM#UND#GVM#DVNGD#IWM#GDWNIGDk#&CHUS#E$EIGUS$#US)DUS*#VOFF#KVS%#(VS+GD$QPKUE#%QPKnH#$##C$#%#%##nH#$##C'#%#&##nO%FF$#'CD#$%#(#)#UD0%EIGnH#$##C$#%#2##nJ$/$#*C-#%$#'&##nJ$F$#*C3#%$#+1##nL#$#,CE#-#####&#&#&#&#&#&#&#&VRK6&S,/nH#$##C##%#0#.nH#$##C2#%#1##nO%FF$#'CD#$%#(#)#&K;nH#$##C##%#<#-nJ$9$#*C)#%$#'%##nJ$F$#*C=#%$#+;##nL#$#,CE#-#####0#0#0#0#0#0#0#0'C-#j#$s###UJ>k#-C#UREnJ$A$#*C7#%$#'-#+nJ$F$#*Cs#%#%$#+s####nL#$#,CE#-#####8#8#8#8#8#8#8#8'C#+j#.(#$IGDUS$#VRE$$PKE&Q#%PKEnH#$##C$#%#%##nH#$##Cs#*#%#&##nO%FF$#'CD#$%#(#)#&E+%IGDnH#$##C$#%#-##nJ$s#2$#*C,#%$#'&##nJ$F$#*C.#%$#+s#4##nL#$#,CI#-#####&#&#&#&#&#&#&#&VS-C##EUS%#US.EZS&<;6&$#US/&US0EZS&s#Bs#AA%$#XM)IGDXNEIGD'C$#m#&#j#/C#(CCs#Js#I#j#0C#(Cs#Us#Os#N#j#*L#(Ls#Vs#Ts#S#j#1s#Y##"). Qed.
#[export] Hint Rewrite mkAluwK0B_eqf : bceq.
Lemma mkAluwKB_eqf : forall fk, mkAluwKB (mkbc fk) = mkAluwK fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluwK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluwK0); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.foldKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.foldK); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.foldKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwK0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwK0B_eqf)|] [|@b; @a; @op; @e; @x1; @x0; @x; @fk|] "##R#(#9#/###&#$#%#0#2#.#4#'#7#6#3#+#,#8#9#:#;#1#5#-&#6$#7&#8(UPQk#$CCk#%C##DUH#UID#FVH#DVIFD#GWH#FDWIGFDk#&J,UKE#LWDEGFVN$#XKLEGFVML#$C%#j#'*#k#'CCUMEUD($C#(j#'&#XKEGFDVME#VRC##EUN#US#EZO-,)&$#US$&US%EZO981%$#XH)GFDXIEGFD$C$#m#&#j#(C#%CCA@#j#)C#%Cs#,s#&s#%#j#*J#%Js#-s#+s#*#j#+s#0##"). Qed.
#[export] Hint Rewrite mkAluwKB_eqf : bceq.
Lemma extK0B_eqf : forall fk, extK0B (mkbc fk) = extK0 fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.extK0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.extK0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Arith.PeanoNat.Nat.leb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf)|] [|@e; @sx; @p; @lo; @hi; @x; @n0; @v; @z; @n; @op; @a; @b; @k; @i; @o; @fk|] "##_#,#I#2#'###$#(#9#%#G#&#7#)#8#:#H#4#3#5#B#;#/#0#>#<#D#F#E#A#@#?#+#*#I#J#K#6#1#=#C%#G$#H$US&S'UQEUR#US#EVNHHUL#k#$C#UOF#S(############VS)F#UDE$S*US$#$$$#US$#US+DVS,$#VS-(#VS.#)nJ#$#%HM#%###$VS/E#nJ#$##C##%#K#S0nN%HH$#&CE#$%#'#(#nL$<$#)C0#%$#&##GnJ#$##C2#%###GnP#$#'CI#%##$#*MnC#$#+CF#+$#,I$#-I&#.#/#0D&#.#/#0D&#.#/#0D&#.#/#0D'#%#'#-#$#'#%#1#2#-GVOMEnL$A$#)C##%$#&(#GnJ#$##C7#%###GnP#$#'CI#%##$#*MnC#$#+CF#+$#,I$#-I&#.#/#0D&#.#/#0D&#.#/#0D&#.#/#0D'#%#'#-#$#'#%#1#2#-GWS%C(#j#3s#$#VOGEnJ#$##C1#%#K#S1nN%HH$#&CE#$%#'#(#nL$s#*$#)C%#%$#&##DnJ#$##C@#%###DnP#$#'CI#%##$#*GnC#$#+CE#+$#,F$#-F&#.#/#0K&#.#/#0K&#.#/#0K&#.#/#0K'#%#'#-#$#'#%#1#2#-DVS2C#UQFUS3#US4FZS5s#0s#/.&$#VR&EVS#FEWS%C$#m#&#j#)C#YS6CCs#:s#9#j#4s#=##"). Qed.
#[export] Hint Rewrite extK0B_eqf : bceq.
Lemma extKB_eqf : forall fk, extKB (mkbc fk) = extK fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.extKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.extK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.extK0); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.foldKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.foldK); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.foldKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.extK0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.extK0B_eqf)|] [|@v; @e; @x; @fk|] "##F#&#6#,#$###1#%#4#-#/#3#0#)#*#5#6#7#8#+#.#2%#4$#5&UMN#EUI#UJEk#$CCUFD#GUEDVK$#VFGDVHG#$C%#j#%*#k#%CCUHDUE($C#(j#%&#VFDEVHD#VOC##DUK#UPDZL-,)&$#UQ&URDZL981%$#VI)EVJDE$C$#m#&#j#&C#YS#CCA@#j#'s#$##"). Qed.
#[export] Hint Rewrite extKB_eqf : bceq.
Lemma flat_scB_eqf : forall fk, flat_scB (mkbc fk) = flat_sc fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.flat_scB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.flat_sc); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCFlat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf)|] [|@n; @e; @p; @lo; @hi; @x; @o; @x0; @fk|] "##v#)#N###$#9#%#1#=#8#7#'#0#2#4#:#&#,#<#A#(#?#B#K#I#;#.#/#-#6#C#D#E#M#J#N#O#P#5#@#L#>#H#G#F#3*#G%#H$#I%#J$#K%#L&#M$UQS,UQGk#$L#)CUM#UNC)DVM#CVNDCVIEEUJ#k#%S-#UOFURFUC#US#S$#D#%S%##C%US&K#$#%#S.nH#$##H'#%###S/US0G&K'S$#(G#%nH#$##<'#%#&##nI%EE$#&=C#$%#'#(#&D'F#(G#*nJ$9$#)A4#%$#&&##VOP6$S1US'#$$$#$#$#$#US'#VS2)#%9#VS(=#nH#$##s#.##%#8#5nI%EE$#&s#/C#$%#'#(#nJ$s#($#)s#00#%$#&##2WS)s#12#j#*s#(#URDVOF#US#K#D#%S%##C%US&P#$#%#2VS('#&P'K#(G#s#)nH#$##s#@&#%#s#*##nI%EE$#&s#AC#$%#'#(#&C'D#(G#s#.nJ$s#=$#)s#E3#%$#&&##VS3s#F#)FUS4#US5FZS6s#@s#?:&$#WM&DCWNFDCWS)s#M$#m#&#j#+L#YS*Ls#Ps#Js#I#j#)S+#YS*S+s#Qs#Os#N#j#,s#T##"). Qed.
#[export] Hint Rewrite flat_scB_eqf : bceq.
Lemma wr_coveredB_eqf : forall fk, wr_coveredB (mkbc fk) = wr_covered fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.wr_coveredB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.wr_covered); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xlo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf)|] [|@n; @a; @kn; @x0; @x; @l; @a0; @kb; @kk; @k; @w; @v; @n0; @k0; @lo; @hi; @e; @m; @len; @a1; @n1; @a2; @n2; @c; @b; @k2; @b2; @k1; @b1; @o; @IH; @rest; @K; @fk|] "#$V#/#Q#7###$#%#(#)#3#'#&#5#E#K#F#6#8#:#J#Q#.#-#O#P#>#B#A#G#*#M#L#N#+#2#=#,#R#S#;#9#<#4#C#?#D#I#H#@/#H$#I&#2'#1%#2%#J(#K%#L&#M$#N$#O%#P)US2Ik#$PCk#%L##DUQ#URD#F&#D'FD$)$#j#&,##EUS3I&$#'E$WQ+%DWRF&D%K'EDVS)C#j#'P#(PC'&#j#(L#(L7+*##K&#D'KD$:$##J*IFE&$#'J$#G*IKFWQ$#DWRG$D'HKVKGJVFJKUS*HVS+#E+H)D#nC#$##C%#%###M#S%VS,#F+S-,H-$#-ED)$#nS#$O$#(C(#%$#)##MnC#$##C+#%###M,GUS.#[S/-20#EDFVJHGnC#$##C$#%#N##nC#$##C(#%#N##nL#$#*CE#$%#+#,#nI#$#-CG#-&#*#.#/9%#*#08&#*#0#19%#2#38%#4#58&#4#2#39%#*#6#'#7#8#9#:&&#*#0#;9%#*#08%S&S-GJ%S4HJKVS097VS'S%FnS#$O$#(C##%$#)1#MnC#$##C%#%###M[S(S%></EDF%S%S1HGnC#$##C$#%#N##nC#$##C&#%#N##nL#$#*CE#$%#+#,#nI#$#-CG#-&#*#.#/-%#*#0,&#*#0#1-%#2#3,%#4#5,&#4#2#3-%#*#6#'#7#8#9#:&&#*#0#;-%#*#0,$C/#j#<s#I#k#:S$Ck#=O#k#>S$#k#8S$#k#?O#k#@S$#US(HZJs#-s#+>EDFnC#$##C##%#N#1nC#$##CB#%#N##nL#$#*CE#$%#+#,#nI#$#-CG#-&#*#.#/;%#*#0:&#*#0#1;%#2#3:%#4#5:&#4#2#3;%#*#6#'#7#8#9#:4&#*#0#;;%#*#0:$C#1j#<*#US#Ok#4S$#US'HUJFnS#$O$#(C##%$#)s#-#MnC#$##Cs#5#%###MnC#$##C##%#N#<nL#$#*CE#$%#+#,#nI#$#-CG#-&#*#.#/s#&%#*#0s#%&#*#0#1s#&%#2#3s#%%#4#5s#%&#4#2#3s#&%#*#6#'#7#8#9#:?&#*#0#;s#&%#*#0s#%$C#<j#A+#%S1GKFUS*GVS+#E+G)D#VS0%#VS'S&F-s#Ds#8)#s#=nS#$O$#(C%#%$#)##MnC#$##C'#%###M,JUS.#[S(S&.,#EDFnC#$##C##%#N#s#7nC#$##C'#%#N##nL#$#*CE#$%#+#,#nI#$#-CJ#-&#*#.#/s#9%#*#03&#*#0#1s#9%#2#33%#4#53&#4#2#3s#9%#*#6#'#7#8#9#:s#:&#*#0#;s#9%#*#03VS)C##HUS,#US5H.BA9&$#US/&US6H.s#/s#.s#'%$#&)K.s#~s#]s#7$#F*IJKXQ,#ED%H$ED$C$#m#'#j#'P#(PCs#fs#e#j#(L#(Ls$,s#ls#k#j#Bs#p#j#Cs$/#j#DI#YS7Is$'s#w#Dj#&s$2#(s$3s$1s$/s$.#j#Es$4##"). Qed.
#[export] Hint Rewrite wr_coveredB_eqf : bceq.
Lemma storeok_scB_eqf : forall fk, storeok_scB (mkbc fk) = storeok_sc fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.storeok_scB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.storeok_sc); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.wr_covered); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCStoreOk); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.wr_coveredB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.wr_coveredB_eqf)|] [|@n; @a; @kn; @b; @l; @x0; @x; @fk|] "##T#'#<#%###$#4#/#.#&#0#2#-#*#5#7#:#9#3#,#+#8#;#<#=#>#1#6&#:$#.'#;&UMS$UMGk#$H##DUJ#UKD#EVJ#DVKEDk#$HFk#%L#k#&-#UNC#IUO#WD#CEUS%GVPCEWQG#$nF#$##4&#%#%##$IICEnF#$##6##%#'#%%7%#j#'.#$IDCEnF#$##:##%#+#)%;#'j#(=#$CCEDVPEDWQG#0nF#$##@%#%#1##VS&A##CUO#US'CZRs#&C+&$#US(&US)CZR>=2%$#WJ)EDWKCED%s#+$#m#&#j#)H#YS#Hs#.s#(s#'#j#*L#YS#Ls#/s#-s#,#j#+s#2##"). Qed.
#[export] Hint Rewrite storeok_scB_eqf : bceq.
Lemma conc_exprB_eqf : forall fk, conc_exprB (mkbc fk) = conc_expr fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.conc_exprB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.conc_expr); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.concretize); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB_eqf)|] [|@e; @x; @v; @z; @n; @op; @a; @b; @sx; @lo; @e0; @k; @i; @o; @fk|] "##L#*#:#0#$#5#6#%###'#(#&#2#1#3#7#8#-#.#9#)#:#;#<#4#/$#/%UQRULHUM#UNHUEFk#$C#UODUDGUS#HnE$F$#%C$#%$#&##GUKInE$F$#%C##%$#&%#IUIJnE$F$#%C##%$#&'#JnC#$#$CD#+$#'G$#('&#)#*#+%&#)#*#+%&#)#*#+%&#)#*#+%'#,#-#(#.#'#,#/#0#(##KGnE$F$#%C##%$#&*#G#JInE$F$#%C##%$#&,#I#S$JnE$F$#%C##%$#&.#JnC#$#$CD#+$#'G$#('&#)#*#+%&#)#*#+%&#)#*#+%&#)#*#+%'#,#-#(#.#'#,#/#0#(#WPC*#j#14##GDnE$F$#%C##%$#&3#D#IKnE$F$#%C##%$#&5#KnC#$#$CH#+$#'D$#(%&#)#*#+#&#)#*#+#&#)#*#+#&#)#*#+#'#,#-#(#.,'#,#/#0#(,VS%C#ULDUS&#US'DZS(>=,&$#VM&HVNDHWPC$#m#&#j#%C#YS)CCs#'s#&#j#2s#*##"). Qed.
#[export] Hint Rewrite conc_exprB_eqf : bceq.
Lemma enum_branchB_eqf : forall fk, enum_branchB (mkbc fk) = enum_branch fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.branch_cond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.enum_branchB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.enum_branch); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.concretize); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.cond_probe); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.negb); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB_eqf)|] [|@b; @a; @e; @pos; @x; @v; @o; @x1; @x0; @fk|] "##V#*#C#$#1###3#%#2#&#4#6#8#9#C#;#:#0#-#.#?#@#>#A#=#<#B#)#(#D#E#F#7#5#/%#A$#B(URS#UHFk#$D#k#%D##EUJ#UKE#CVJ#EVKCE#GWJ#CEWKGCEUHLk#&D#UMIWOIGCUGCVS$ES%VS&#S'US(#nF#$#'FC#%###$VS)F#US*FnH$L$#(9)#%$#)$##nN%DF$#(:+#$%#&#'#VMS+CnH$L$#(<##%$#)'#&nN%DF$#(=.#$%#&#'#WP>&#j#*2#WOGCEVMS,CnH$L$#(B##%$#)-#,nN%DF$#(s##%#$%#&#'#VS-s#$##IUS.#US/IZS0;:+&$#XJ&GCEXKIGCEWPs#+$#m#&#j#+D#$Ds#.s#$s###j#,D#$Ds#/s#)s#(#j#(Q#$Qs#0s#.s#-#j#-s#4##"). Qed.
#[export] Hint Rewrite enum_branchB_eqf : bceq.
Lemma to_saddrKB_eqf : forall fk, to_saddrKB (mkbc fk) = to_saddrK fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.to_saddrKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.to_saddrK); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.concretize); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.split_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.to_saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.concretizeB_eqf)|] [|@imm; @e; @x; @v; @e0; @z0; @n; @op; @a; @b; @sx; @lo; @e1; @k; @i; @z; @o; @x0; @fk|] "##g#-#E#5#4#:#3#$###(#)#%#@#*#'#6#8#&#+#D#;#=#<#2#0#1#C#B#,#E#F#G#9#A#>#?#7(#A$#B%#C&#4%#D$US(S)k#$DC'HUO#UPH'GVO#HVPGHUEDk#%F#US$KUS%K$IN#N%LI#UQ##S*VS+#HnE$D$#&C%#%$#'##(#J%LM#UI#$MJnE$D$#&C$#%$#'(###M%LR#UJ#$RMnE$D$#&C$#%$#'-##nF#$#(CG#+$#)3$#*-&#+#,#-(&#+#,#-(&#+#,#-(&#+#,#-('#.#/#*#0#'#.#1#2#*#nS#%FD$#&C5#$%#(#3#&J3nE$D$#&C##%$#'1#6&R/nE$D$#&C##%$#'3#.&S,,nE$D$#&C##%$#'5#+nF#$#(CG#+$#);$#*'&#+#,#-%&#+#,#-%&#+#,#-%&#+#,#-%'#.#/#*#0#'#.#1#2#*#nS#%FD$#&C=#$%#(#3#WS&C+#j#4A#US%G$NQ#Q%LN#&I#nE$D$#&C##%$#'?#&#I%LJ#&M#$JInE$D$#&C$#%$#'s#$##nF#$#(CG#+$#),$#*(&#+#,#-#&#+#,#-#&#+#,#-#&#+#,#-#'#.#/#*#04'#.#1#2#*4nS#%FD$#&C.#$%#(#3#VS-C#'KUS.#US/KZS0s#3s#24&$#WO&GHWPKGHWS&C$#m#&#j#5D#YS'DCs#<s#;#j#&F#YS'Fs#Cs#As#@#j#6s#E##"). Qed.
#[export] Hint Rewrite to_saddrKB_eqf : bceq.
Lemma amo_alignedbB_eqf : forall fk, amo_alignedbB (mkbc fk) = amo_alignedb fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@LinuxProcessSemantics.Riscv.Instr.awidth); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.amo_alignedbB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.amo_alignedb); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_lowbits_kn); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_lowbits_knB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_lowbits_knB_eqf)|] [|@wd; @k; @e; @x; @r; @o; @x0; @fk|] "##L#'#?###/#4#%#$#.#5#0#2#-#6#>#:#8#7#,#*#+#9#;#<#=#&#?#@#A#3#1$#>$US#S$k#$HD#CUJ#UKC#GVJ#CVKGCUIEk#%E#k#&L#UMFUS%OUP#US&OUP#nH#$#$EG#%#%##VCF#VS'CS(nI$E$#'D$#%$#(##NWMS)F&nI$E$#'D##%$#(%#NWQD%#j#)/#nH#$#$EC#%#-#+WMFG#nI$E$#'D##%$#(*#NVS*D##FUS+#US,FZS-76*&$#WJ&GCWKFGCWQD$#m#&#j#*H#YRHDA@#j#'L#YRLs#(s#&s#%#j#+s#*##"). Qed.
#[export] Hint Rewrite amo_alignedbB_eqf : bceq.
Lemma amo_newvalB_eqf : forall fk, amo_newvalB (mkbc fk) = amo_newval fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.Riscv.Instr.awidth); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.amo_newvalB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.amo_newval); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluwK); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluK); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwKB_eqf)|] [|@src; @old; @aop; @b; @a; @op; @wd; @o; @e; @x2; @x1; @x0; @x; @fk|] "##a#*#=#3###$#%#&#'#2#0#1#4#6#(#8#)#;#:#7#-#.#<#=#>#?#5#/#9&#:$#;(#<&US$S%UKIk#$CCk#%C#k#&%##DUL#UMD#EVL#DVMED#FWL#EDWMFED#GXL#FEDXMGFEDk#'CCk#(C#k#)I#UOHWEDGF#PXR#DGFnJ#$#*CN#%#%##nK$I$#&CG#%$#+##EXOPDGFXQPDGFnJ#$#*CN#%#$##nK$I$#&CG#%$#+##E%C'#j#,.#UQHnJ#$#*CN#%#)#.nK$I$#&CG#%$#+##E%C#(j#,3#XONDFEXQNDFEnJ#$#*CH#%#$##nK$I$#&CF#%$#+##DVS&C##HUR#US'HZS#</+&$#US(&US)HZS#?>3%$#YL)GFEDYMHGFED%C$#m#&#j#-C#$CCs#)s#(#j#.C#$Cs#8s#.s#-#j#/s#:#$s#;s#9s#3s#2#j#0J#$Js#:s#8s#7#j#1s#?##"). Qed.
#[export] Hint Rewrite amo_newvalB_eqf : bceq.
Scheme kc__4 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sentry Sort Prop.
Scheme kc__5 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr Sort Prop.
Lemma log_lookupB_eqf : forall fk, log_lookupB (mkbc fk) = log_lookup fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.log_lookupB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.log_lookup); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__4); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@kc__5); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rel_lit); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.LHit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkExt); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.log_bytes_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lit_of_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.LStuck); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apartB); constr:(@Stdlib.Lists.List.tl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCDisj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rangerel); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apartB_eqf)|] [|@acc; @hints; @sx; @n; @rk; @rb; @log; @x4; @x3; @x2; @x1; @x0; @x; @l; @s; @e_val; @e_width; @bs; @b; @d; @n2; @k2; @b2; @n1; @k1; @b1; @IH; @rest; @v; @w; @kk; @kb; @a_off; @a_base; @e_addr0; @e_addr; @a; @fk|] "#%b#;#c###$#%#'#&#(#G#E#)#A#H#J#*#C#B#-#.#+#D#,#7#/#F#]#0#8#>#c#Q#1#d#N#2#3#4#5#6#V#Y#[#\#^#_#U#?#M#Z#:#9#e#R#O#K#I#P#@#T#L#S#b#W#X#`#a3#X$#Y&#Z(#[%#-%#.%#\&#]&#.+#^$#=$#_$#`&#a%#b'##)-S?-L-J-S)k#$#Ik#%%#k#&J#k#'S%#k#(P#k#)Q##CUM#UNC#E'#C(EC))$#j#*2##DUS@L'$#(D$WM+%CWNE&C#GXM#(DCXNG)DC#FYM#+EDCYNF,EDC#HZM#.GEDCZNH/GEDC#K[M#1FGEDC[NK2FGEDC+O3HFGEDCVS2I#j#+s#%#%s#&I'&#j#,s#(#%s#)s#',+#j#-J#%Js#(10#j#.S%#%S%s#)65#j#/P#%Ps#*;:#j#0Q#%Qs#+?>#'9C(FC)s#-$#$LED':#(H$)s#1$#k##'#k#1s#;#j#2L##R'#C(RC)s#8$##S#*FGE$L#D'%#(S#$)s#>$#k##)#k#1s#H#k#3Q#k#4S%#j#2S/##S+'#C(S+C)s#G$##S0&HF*#GE$L#D'&#(S0$#S3&KH*#FG$L#EWM&#CWNS3$C#S4&OK*#HF$L#GXM&#DCXNS4$DC#S5&S$O*#KH$L#FYM&#EDCYNS5$EDC#S6&S&S$*#OK$L#HZM&#GEDCZNS6$GEDC#S7&RS&*#S$O$L#K[M&#FGEDC[NS7$FGEDC(S'O.F.RZS8KH$S(S##USACXS9F#HR/#EG2KHFGED-P&S(S#*#RS&$L#S$XS:#KHFWS;FHC/#EGnS<$)$#0I%#%$#5##S*#S,[S=#KH2S(S#10JE,F,R1s#4$.#$S)#D2KHFG'#0JF,K&S0S+,S(1s#/%$#$S)#GZES$OKH(#nJ#$#6ID#%###S*nS-$J$#%IE#%#+%#6#1#nJ#$##I2#%#<##nS.#$#0IA#'$#7>#=#5##+S,S$KHFGED[S1S,KHs#%S(S#s#$+S,S$KHFG51+SBRS$OKH0+nJ#$#6ID#%###S*nS-$J$#%IE#%#%%#6#1#nJ#$##I'#%#(##nS.#$#0Is#)#'$#7s#&#)#=##)I+#j#1s$<#k#8PJk#9P#k#:Q#k#;P#k#<P#k#=Q#US1S'2KHs#5S(S#s#4nJ#$##I##%#4#/nS.#$#0Is#5#'$#7s#2#5#s#)##)I#/j#6(#.G.S&ZS8HF$S#R#XS9Gs#:FS&/#DE+S'OHFGEDC&S#R*#S&S$$L#OXS:#HFGWS;GFC/#DEnS<$s#?$#0I%#%$#5##S*[S1S'HF/S#R.0JD,G,S&1s#o$-#$S)#C+S'OHFGE'#0JG,H&S+S(,S#1s#j%$#$S)#E+SCS&OKHF(#nJ#$#6ID#%###S*nS-$J$#%ID#%#+%#6#1#nJ#$##I2#%#:##nS.#$#0I>#'$#7<#;#4##VS2I##S'US=#USDS'ZS>s#,s#+s#&&$#'&OZS>s$ns#`s#4$#K\M(@HFGEDC+S'AHFGEDC)I$#m#&#j#+s$y#%s$zIs#hs#g#j#,s$|#%s$}s${s#ps#o#j#-J#%Js$|s#xs#w#j#.S%#%S%s$}s$$s$##j#/P#%Ps$~s$,s$+#j#0Q#%Qs%#s$4s$3#j#>s$:#j#?s%,#j#@Q#j#AS%#j#BP#j#CQ#V#DCj#DP#j#EQ#WSEs$G#Cj#FS/#W#EDCj#3Q#j#4S%#j#GS/#WSFs$\#Cj#HL#YSGLs%,s$h#Cj#*s%=#%s%>s%6s%4s%3#j#Is%@##"). Qed.
#[export] Hint Rewrite log_lookupB_eqf : bceq.
Lemma know_lookupA0B_eqf : forall fk, know_lookupA0B (mkbc fk) = know_lookupA0 fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupA0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookupA0); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rel_lit); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.LHit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkExt); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rangerel); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCInside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EBlob); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.LStuck); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.img_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lit_of_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.fill_lit); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf)|] [|@acc; @hints; @sx; @n; @rk; @rb; @kn; @x4; @x3; @x2; @x1; @x0; @x; @d; @a; @kb; @kk; @b; @hs; @delta; @len; @l0; @n0; @op; @sx0; @lo; @e; @k; @i; @p; @z; @k0; @bs; @lo0; @K; @w; @v; @hi; @m; @a1; @n1; @a2; @n2; @c; @l; @k2; @b2; @k1; @b1; @o; @IH; @rest; @segs; @fk|] "#)I#;#s#G#E#$###-#*#.#+#,#%#&#)#'#/#0#(#1#B#>#C#2#W#?#3#4#i#H#J#F#V#h#6#7#5#f#e#8#D#M#N#T#X#`#j#k#n#9#s#q#r#g#\#A#U#Y#Z#[#p#m#:#t#u#K#S#O#a#I#@#b#^#l#R#d#c#_#]#Q#L#o#PA#b&#>,#c&#d%#e$#f(#g%#h'#i&#S*#j$#k%#l'#m%#n$#o)#p&#V*#q$#T%#5$#=&#>&#*)#2)#()#+)#.)#U%#r)7S)7SG7D7S/k#$#Ck#%%#k#&D#k#'S8#k#(S&#k#)S$#k#*,#'FUS-#US.F'EVS-#FVS.EF'M8#LF9MLF3-$#j#*7#'LUS9S)8$E#9LE$XS-+L%FXS.ML&F'OYS-#M(EFYS.OM)EF'RZS-#O+LEFZS.RO,LEF'N[S-#R.MLEF[S.NR/MLEF'H\S-#N1OMLEF\S.HN2OMLEF$JH3ROMLEFVS:C#j#+s#)#(s#*C'&#j#,s#,#(s#-s#+,+#j#-D#(Ds#,10#j#.S8#(S8s#-65#j#/S&#(S&s#.;:#j#0S$#(S$s#/?>#8<MF9OMF3s#1$#%S)LE8=O#9RO$%S)MLXS-=R#FXS.NR$F%S)OMYS-=N#EFYS.HN$EF'J%S)ROZS-$H#LEFZS.JH$LEF'K%S)NR[S-$J#MLEF[S.KJ$MLEF'G%S)HN\S-$K#OMLEF\S.GK$OMLEF9IGH-K-M2IG$EF#USHFXS;K#GM##HJ;IGKJHNnS0#$#0C'#'$#1$######nS(#$#2CL#$%#3#4#VS<FSI2IG,LE#USJSK##HJ'S+1K4$IG#LEM#'NHUS9D;IGKJ#N0QP1I0OM*%$#R%S/#J#/#F<QPIGFJnD#$#5CE#%#$##nS%$D$#%CH#%#+%#5#6#nD#$##C/#%#.##nS0#$#0C5#'$#73#9#9##'S24#QP-OMR#7JK<QPIG2J0S'S#1Q0NR*%$#H%S/#G#>#F=S'S#QPFGnD#$#5CE#%#$##nS%$D$#%CK#%#+%#5#6#nD#$##C.#%#-##'S31P4$S#Q#RON#s#&KG:S#QPIAK0S*S'1S#0HN*%$#J%S/#I#s#-#FZGS*S'S#QFInD#$#5CE#%#$##nS%$D$#%CG#%#+%#5#6#nD#$##C.#%#-##nS$#$#8CL#+$#9@$#:A&#;#2#52&#;#2#52&#;#2#52&#;#2#52'#<#=#:#>#'#<#?#@#:#nS(#$#2CE#$%#3#4#VS=IE&FG-G)I#)Es#:&$#.IE/KM#G##HJ&'I>PIGKJHnD#$##C$#%###S6nD#$##C)#%#&##VS5S&S&'S4?#O-Q)S##)OE&$#nS5%S&S&$#ADF#$%#=#B#nS,$*$#0D(#%$#A##S1>PIGKs#DH.QM/IR#P0S#Q*#s#,s#DN%S/#K#&#F:S#QPIFKnD#$#5CE#%#$##nS%$D$#%CJ#%#+%#5#6#nD#$##C-#%#:##?s#4N-S')S*#)NE&$#nS5%S&S&$#ADF#$%#=#B#nS,$<$#0D(#%$#A##S1#2KG.S'R/QH#S#*s#9s#8s#FJ%S/#I#%#FnD#$#5CE#%###s#6nS%$D$#%CG#%#s#>%#5#6#nD#$##C+#%#*##'S7?#H-S*)S+#)HE&$#nS5%S&S&$#ADF#$%#=#B#nS,$s#-$#0D(#%$#A##S1.S#O/PN#Q##GI=S'S#QPs#jG.S*N/S#J#S'0S+S*1S'*$#s#MK%S/#P#'#FZIS+S*S'S#FPnD#$#5CE#%#$##nS%$D$#%CI#%#,%#5#6#nD#$##C1#%#.##nS$#$#8CM#+$#9s#>$#:s#*&#;#2#5:&#;#2#5:&#;#2#5:&#;#2#5:'#<#=#:#>#'#<#C#@#:#nD#$##Cs#J#%###s$&nD#$##Cs#L#%###s$'nS(#$#2CL#$%#3#4#&LJ-H)J#&#EnD#$##D&#%###S17S&WS>S#JHWS?HJF##RNnS,$&$#0C%#%$#D##S6ZMKJHNROnD#$##C)#%#$##ZOGKJHNRnS&#$#BCF#&#$$#A#$#A#nS$#$#)CJ#+$#B#$#:&&#;#2#5s$7&#;#2#5s$7&#;#2#5s$7&#;#2#5s$7'#<#E#:#>s#R'#<#?#@#:s#RZLJHNROM2PIs#\LEs$6+GIO##JK1G4s#TPI#LEO+KGM##HJ+IPR##s#KFnD#$#5CE#%###s#JnS%$D$#%CJ#%#s#R%#5#6#nD#$##C)#%#'##nS0#$#0C.#'$#7,#s#`#s#`##4s#|S#Qs#{OMN#)KG+QS#H##s#BFnD#$#5CE#%###s#unS%$D$#%CG#%#s#}%#5#6#nD#$##C(#%#'##4s#AS'S#s$0ROH+PQN##GI+S#S'J##s#4FnD#$#5CE#%###s#3nS%$D$#%CI#%#s#<%#5#6#nD#$##C)#%#'##nS$#$#8CM#+$#92$#:3&#;#2#5+&#;#2#5+&#;#2#5+&#;#2#5+'#<#=#:#>#'#<#?#@#:#nS(#$#2CL#$%#3#4#nS)#$#FCK#-&#2#G#Hs$U%#2#8s#}&#2#8#?s#1%#=#IB%#>#JA&#>#=#Is#&%#2#:A'#K#L#M#Ns#$&#2#8#O#%#2#:A$S+S*QIGKJHNnS0#$#0Cs$]#'$#1s$Z######nS(#$#2CL#$%#3#4#5SLUS@#5$5#5#5#5#US@#VSM)#VS<F#2IGs$kLE#,S+IGs$^LEM$S+S*QIGKJs$\N$S2S4S'QPIGFJnD#$#5CE#%#s$W##nS%$D$#%CH#%#%%#5#6#nD#$##C'#%#s$a##nS0#$#0C)#'$#7s$f#6#6##,S2QPs$_OMR$S2S4S'QPIGs$cJ$S7S3S+S'S#QPFGnD#$#5CE#%#s$O##nS%$D$#%CK#%#%%#5#6#nD#$##C'#%#s$X##,S3S#Qs$LRON$S3S2S*S#QPIs$iK$SAS7S4S*S'S#QFInD#$#5CE#%#s$F##nS%$D$#%CG#%#%%#5#6#nD#$##C'#%#s$O##nS$#$#8CL#+$#9/$#:0&#;#2#5)&#;#2#5)&#;#2#5)&#;#2#5)'#<#=#:#>#'#<#?#@#:#nS(#$#2CE#$%#3#4#)E9&s$B#&$I$S4S+S#PIGKJHnD#$##C$#%###S6nD#$##C&#%#s$A##6S4OnS,$s$>$#0D##%$#As$7#S1$S4S+S#PIGKs$xH$S3S2S*S#QPIFKnD#$#5CE#%#s$2##nS%$D$#%CJ#%#%%#5#6#nD#$##C'#%#s$H##6S3NnS,$s$E$#0D##%$#As$,#S1nD#$#5CE#%#s$&#7nS%$D$#%CG#%#9%#5#6#nD#$##C%#%#s$-##6S7HnS,$s$J$#0D##%$#As#|#S1$S7S3S+S'S#QPs%(G$SNSAS2S+S*S'S#FPnD#$#5CE#%#s#s##nS%$D$#%CI#%#%%#5#6#nD#$##C'#%#s#}##nS$#$#8CM#+$#96$#:/&#;#2#5*&#;#2#5*&#;#2#5*&#;#2#5*'#<#=#:#>#'#<#C#@#:#nD#$##Cs$]#%###s#?nD#$##Cs$_#%###s#@nS(#$#2CL#$%#3#4#VSBs#qs#n$S'S#IKJHNROnD#$##C$#%#s#j##$S*S'PGKJHNRnS&#$#BCF#&#$$#A#$#A#nS$#$#)CJ#+$#B#$#:&&#;#2#5s#G&#;#2#5s#G&#;#2#5s#G&#;#2#5s#G'#<#E#:#>A'#<#?#@#:A$S#QGJHNROM2PIs$fLEs#=,S4PIs#fLEOnD#$#5CE#%#s#b#?nS%$D$#%CJ#%#A%#5#6#nD#$##C%#%#s#f##nS0#$#0C'#'$#7s#k#s#(#s#(##,S3S#Qs$~OMNnD#$#5CE#%#s#_#s#3nS%$D$#%CG#%#s#5%#5#6#nD#$##C%#%#s#c##,S7S'S#s%0ROHnD#$#5CE#%#s#[#<nS%$D$#%CI#%#>%#5#6#nD#$##C%#%#s#_##nS$#$#8CM#+$#9+$#:,&#;#2#5'&#;#2#5'&#;#2#5'&#;#2#5''#<#=#:#>#'#<#?#@#:#nS(#$#2CL#$%#3#4#nS)#$#FCK#-&#2#G#Hs#W%#2#8s#7&#2#8#?:%#=#I4%#>#J3&#>#=#I8%#2#:3'#K#L#M#N6&#2#8#O#%#2#:33Cs#[#j#Ps&E#k#NS$Dk#QS&#k#RS$#k#LS$#k#SS&#k#TS$#USCI;IGs%ULEMnD#$##C##%#s%T#s#RnS0#$#0Cs%[#'$#7s%Y#s#e#s#e##<QPs%ROMRnD#$##C##%#s%G#s#N:S#Qs%;RONnD#$##C##%#s%:#s#JnS$#$#8CL#+$#9'$#:(&#;#2#5%&#;#2#5%&#;#2#5%&#;#2#5%'#<#=#:#>#'#<#?#@#:#nS(#$#2CE#$%#3#4#nD#$##Cs%&#%#s#F#S6nD#$##Cs%+#%#s%(##nD#$##Cs$x#%#s%)#s#@nD#$##Cs$g#%#s$f#s#<nD#$##Cs$W#%#s$T#s#6nS$#$#8CM#+$#9&$#:%&#;#2#5$&#;#2#5$&#;#2#5$&#;#2#5$'#<#=#:#>#'#<#C#@#:#nD#$##Cs%4#%###s#rnD#$##Cs%6#%###s#snS(#$#2CL#$%#3#4#nD#$##Cs$D#%#s$?#s#4nS&#$#BCF#&##$#As#3$#As#3nS$#$#)CJ#+$#B#$#:s#6&#;#2#5s#w&#;#2#5s#w&#;#2#5s#w&#;#2#5s#w'#<#E#:#>s#Q'#<#?#@#:s#Q>PIs$8LEOnD#$##C##%#s$6#s#/nS0#$#0Cs$=#'$#7s$;#s#T#s#T##:S#Qs%NOMNnD#$##C##%#s$1#s#-=S'S#s%ZROHnD#$##C##%#s$+#s#+nS$#$#8CM#+$#9'$#:(&#;#2#5%&#;#2#5%&#;#2#5%&#;#2#5%'#<#=#:#>#'#<#?#@#:#nS(#$#2CL#$%#3#4#nS)#$#FCK#-&#2#G#Hs$#%#2#88&#2#8#?/%#=#I,%#>#Js#;&#>#=#Is#@%#2#:s#;'#K#L#M#Ns#>&#2#8#O#%#2#:s#;3C#s#+j#5s#$#US,s%:k#>S$#USDInS0#$#0Cs%}#'$#7s%{#s$+#s$+#s#tnS$#$#8CL#+$#9#$#:s#u&#;#2#5s#n&#;#2#5s#n&#;#2#5s#n&#;#2#5s#n'#<#=#:#>s#h'#<#?#@#:s#hnS(#$#2CE#$%#3#4#UNOnS,$s%A$#0D##%$#As%:#S1nD#$##C##%#s%G#s#^UJNnS,$s%D$#0D##%$#As%+#S1nD#$##C##%#s%*#s#\UKHnS,$s%G$#0D##%$#As$y#S1nD#$##C##%#s$v#s#XnS$#$#8CM#+$#9s#($#:)&#;#2#5&&#;#2#5&&#;#2#5&&#;#2#5&'#<#=#:#>#'#<#C#@#:#nD#$##Cs%V#%###s$8nD#$##Cs%X#%###s$9nS(#$#2CL#$%#3#4#nS0#$#0Cs$Z#'$#7s$X#s#q#s#q#s#LnS$#$#8CM#+$#9#$#:s#M&#;#2#5s#H&#;#2#5s#H&#;#2#5s#H&#;#2#5s#H'#<#=#:#>s#D'#<#?#@#:s#DnS(#$#2CL#$%#3#4#nS)#$#FCK#-&#2#G#Hs$<%#2#83&#2#8#?&%#=#Is#%%#>#Js#T&#>#=#Is#Y%#2#:s#T'#K#L#M#Ns#W&#2#8#O#%#2#:s#T3C#s#Dj#U9#-J2GK#EFs&AXS;Js&@KM##NHnS0#$#0C%#'$#1##s#^#s#^#s#^nS(#$#2CL#$%#3#4#2GK(LEs$;1J,S*GK#LEM#s&?RN$S*S'PGKJHs&:R0PI*#s$is&8R%S/#H#s&D#F$S4S+S#PIGKFHnD#$#5CE#%#$##nS%$D$#%CN#%#)%#5#6#nD#$##C,#%#+##nS0#$#0C/#'$#7s&D#s#m#s#m##,S4PIs$qOMR*s%\s&)s&2H%S/#K#s&M#FnD#$#5CE#%###s$-nS%$D$#%CJ#%#s$/%#5#6#nD#$##C(#%#s&O##,S2QPs&HRON*s&;s&:s&*J%S/#G#s&T#FnD#$#5CE#%###s$InS%$D$#%CK#%#s$K%#5#6#nD#$##C(#%#s&B##nS$#$#8CL#+$#91$#:2&#;#2#5*&#;#2#5*&#;#2#5*&#;#2#5*'#<#=#:#>#'#<#?#@#:#nS(#$#2CE#$%#3#4#VS=GE&FK)Gs&g&#s$E.GE/JM#K##NH&s$IGnD#$##C##%#s$m#S6nD#$##C(#%#%##6S+O-P)Q#&#s&#nS5%S&S&$#ADF#$%#=#B#nS,$s&*$#0D'#%$#A##S1.PM/GR#I*s&ds&cs&bN%S/#J#%#FnD#$#5CE#%###s$jnS%$D$#%CH#%#s$l%#5#6#nD#$##C*#%#3##6S2N-S#)S'#&#s%{nS5%S&S&$#ADF#$%#=#B#nS,$s&8$#0D'#%$#A##S1#/JK.S#R/PH#Q*s&ds&cs&bJ%S/#G#%#FnD#$#5CE#%###s$rnS%$D$#%CK#%#s$t%#5#6#nD#$##C+#%#*##6S3H&s&-s%wnS5%S&S&$#ADF#$%#=#B#nS,$s&E$#0D%#%$#A##S1.QO/IN#P##KG.S'N/QJ#S#*s&ds&cs&bK%S/#I#%#FnD#$#5CE#%###s${nS%$D$#%CG#%#s$}%#5#6#nD#$##C-#%#*##nS$#$#8CM#+$#9s#/$#:A&#;#2#52&#;#2#52&#;#2#52&#;#2#52'#<#=#:#>#'#<#C#@#:#nD#$##Cs#8#%###s$YnD#$##Cs#:#%###s$ZnS(#$#2CL#$%#3#4#&LH-N)H#&#EVSB&#WS>QHNWS?NHF##ORnS,$s%u$#0C%#%$#D##S6nD#$##C'#%###s$bnS&#$#BCF#&##$#As$h$#As$hnS$#$#)CH#+$#B#$#:s$d&#;#2#5s$g&#;#2#5s$g&#;#2#5s$g&#;#2#5s$g'#<#E#:#>s%N'#<#?#@#:s%N$QPKHNROML+KGO##HJ,S+IGs'DLEO+JKM##NH+GIR##s#<FnD#$#5CE#%###s%GnS%$D$#%CH#%#s%I%#5#6#nD#$##C)#%#'##nS0#$#0Cs%M#'$#7+#s%Z#s%Z##,S2QPs'GOMN#)JK+PQH##s#5FnD#$#5CE#%###s%HnS%$D$#%CK#%#s%J%#5#6#nD#$##C(#%#'##,S3S#Qs'5ROH+IPN##KG+QS#J##s#.FnD#$#5CE#%###s%JnS%$D$#%CG#%#s%L%#5#6#nD#$##C)#%#'##nS$#$#8CM#+$#92$#:3&#;#2#5+&#;#2#5+&#;#2#5+&#;#2#5+'#<#=#:#>#'#<#?#@#:#nS(#$#2CL#$%#3#4#nS)#$#FCJ#-&#2#G#Hs$(%#2#8s#f&#2#8#?s#,%#=#I@%#>#J?&#>#=#Is%&%#2#:?'#K#L#M#Ns%+&#2#8#O#%#2#:?VS:C#'IUSE#USOI@s$Js$Is$3&$#USF&USPI@s$qs$ps$O%$#8)GH@s(`s'ws$y$#N%S)JH]S-,G#ROMLEF$IG$ROMLEF3C$#m#'#j#+s(l#(s(mCs($s(##j#,s(o#(s(ps(ns(*s()#j#-D#(Ds(os(0s(/#j#.S8#(S8s(ps(6s(5#j#/S&#(S&s(qs(;s(:#j#0S$#(S$s(rs(@s(?#j#Vs(C#j#Ws(|#j#FS)#YSQS)s(is(I#Fj#*s)##(s)$s(ws(qs(p#j#Xs)$#(s)%s(xs(vs(u#j#Ys)'##"). Qed.
#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Lemma know_lookupAB_eqf : forall fk, know_lookupAB (mkbc fk) = know_lookupA fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupAB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookupA); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookupA0); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.LHit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_bytes_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lit_of_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.LMiss); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.LStuck); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupA0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupA0B_eqf)|] [|@acc; @hints; @sx; @n; @rk; @rb; @kn; @segs; @x; @bs; @v; @scs; @hints0; @acc'; @hints'; @l; @x6; @x5; @x4; @x3; @x2; @x1; @x0; @fk|] "##u#.#G###$#%#&#:#'#(#)#*#;#=#+#8#6#7#5#?#,#F#B#C#E#@#2#4#9#-#D#G#H#I#>#<#3#1#A'#C$#D(#E$#F&%S*%S+%O%S,k#$#Gk#%%#k#&O#k#'Q#k#(P#k#)R#k#*,##CUL#UMC#DVL#CVMDC#EWL#DCWMEDC#FXL#EDCXMFEDC#HYL#FEDCYMHFEDC#IZL#HFEDCZMIHFEDC#J[L#IHFEDC[MJIHFEDC#K\L#JIHFEDC\MKJIHFEDCk#+s#$;US#N\CNKJIHFED&EDC%PYS&S-S$NKJWS'JKC&#EDVS.DCnS($'$#,G&#%$#-$##nG#$#,G*#&&#.#/#0)%#1#2##S%]S#S$NKJIHFEDnG#$#,G##&&#.#/#0+%#1#2%#S%WS)G%#j#30#]S#NKJIHFEDCYS&S$NKJIWS'IJC&#EDnS($1$#,G%#%$#-##-nG#$#,G'#&&#.#/#03%#1#2##S%VS/G##NUS0#US1NZS2;:-&$#]L&KJIHFEDC]MNKJIHFEDCWS)G$#m#&#j#4s#@#$s#AGs##B#j#5s#C#$s#Ds#Bs#(s#'#j#6O#$Os#Cs#-s#,#j#7Q#$Qs#Ds#2s#1#j#8P#$Ps#Es#7s#6#j#9R#$Rs#Fs#<s#;#j#:s#O#$s#Ps#Gs#As#@#j#,s#P#$s#Qs#Hs#Fs#E#j#;s#S##"). Qed.
#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Lemma sym_readB_eqf : forall fk segs ss, sym_readB segs ss (mkbc fk) = sym_read segs ss fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sym_state); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.scripts); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sym_readB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sym_read); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookupA); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.log_lookupB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_log); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sc_hints); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.extKB); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.flat_scB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sc_dirs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sc_reads); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_know); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EVar); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCReadBase); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.log_lookup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.extK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.flat_sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sentry); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.extKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.flat_scB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.log_lookupB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupAB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupAB_eqf)|] [|@sx'; @n; @a; @acc; @hints; @sx; @rk; @rb; @kn; @segs; @x; @e; @l; @t; @v; @scs'; @hints'; @scs; @log; @x2; @x1; @x0; @ss; @fk|] "#%U#0#d#$#>#%###)#:#8#?#&#'#(#*#E#+#,#;#@#B#3#9#-#F#P#/#.#]#I#L#M#H#W#X#Z#Y#[#_#^#R#4#5#<#D#\#`#a#b#c#d#e#f#6#O#N#Q#A#S#G#J#K#T#U#V#C#7#=5#V'#W%#X&#Y$#5$#Z&#[&#\$#]$#^$#_$#`$#G%#F&#a)#b(#c%#H&'S9'S:'J3D#3#I3#HUS;#k#$R#k#%H#k#&S&#&EWS#CF#WS$CFE&KXS#EC#FXS$ECKF&LYS#KE#CFYS$KELCF&MZS#LK#ECFZS$LKMECF'Rk#'7Ok#($#k#)R#k#%H#k#*S<#k#+D#k#,?#k#-?#US(G&NUS-M*K+KUS.LUS/J\S0('&%EC$#&S'VS)#E4$GM%J#C#Ds#+%#,N-N($#F#s#.I&#.P#s#/H$#$s#/#US1N*M+M\EP%$#LKFC&S*VS)#E4$PN%J#C#Ds#;%#,Q-Q($#F#s#>I&#.S'#s#?H$#$s#?#-P.QUS2#nS%$D$#.D%#%##%#/#0C&S+4#NGXS3NGM%WS4J#C%J%##Ds#L(#,P'DUS/DnS%$D$#.$/#%##%#/#1F(&#F#s#QI(#US51#s#RH$#$s#R#US=s#SnO#$#.s#Ss###&&#2#3#47%#3#4$##nO#$#.s#Ts#4#&&#2#5#(s#(%#5#(##$\S,Ns#:s#9s#8ECs#7s#6/S'E0S'GM%J#C#Ds#]%##s#]I#s#2#s#]H#s#1$s#]#]S(QPs#0s#/s#.LKFC/S*E0S*PN%J#C#Ds#e%##s#eI#s#*#s#eH#s#)$s#e#0S+NG%J#B#Ds#ks#'##s#kI#=#s#kH#<$s#k#nO#$#.s#k0#&&#2#3#4)%#3#4##;nO#$#.s#l9#&&#2#5#(2%#5#(##<)s#m;#j#0s#V#'S>k#6#s#ZUS,G[Fs#Ws#Vs#UECs#Ts#SnO#$#.s#s8#&&#2#3#4s#7%#3#4s#$#s##nO#$#.s#t$#&&#2#5#(s#H%#5#(##s#$)s#u#+j#0(#k#%Hs#{k#&S&#US6GVKGM%J#C#Ds$$s#Z##s$$I#s#U#s$$H#s#T$s$$#VMPN%J#C#Ds$*s#P##s$*I#s#K#s$*H#s#J$s$*#VLNG%J#s#C#Ds$0s#H##s$0I#s#>#s$0H#s#=$s$0#nO#$#.s$0s#1#&&#2#3#4)%#3#4##s#<nO#$#.s$1s#:#&&#2#5#(0%#5#(##s#=)s$2#s#$j#09#k#2DDUS7GUKE#Ds$;#s#=#s$;I#s#l#s$;H#s#k$s$;#UME#Ds$@#s#:#s$@I#s#a#s$@H#s#`$s$@#nO#$#.s$@s#A#&&#2#3#4#%#3#4s#4#s#LnO#$#.s$As#J#&&#2#5#()%#5#(##s#M)s$B#s#4j#/1#US-L*E+EUS.K\S,G&%$CF#s$)/QE0QML%J#C#Ds$P%#,G-G($#F#s$SI&#.N#s$TH$#$s$T#US1G*L+L]S(PN%$#KEFC/S+E%Js#RC#Ds$^$#(s#ps#zF#s$_I$##s$_H#s#{$s$_#US2s$5nS%$D$#.Ds$9#%##%#/#0CXS3GML#WS4J#C%Js#j##Ds$h&#nS%$D$#.s#ys$>#%#s#x%#/#1F(s$@#F#s$jI%#US5s$>#s$kH$#$s$k#nO#$#.s$k6#&&#2#3#4/%#3#4##s#wnO#$#.s$ls#&#&&#2#5#(;%#5#(##s#xVS?s$m#&GUS)#US@G1s#?s#>s#0&$#US8&USAG1s#Zs#Ys#C%$#US0)USBG1s#es#ds#_%$#USC,USDG1s$bs$as#j%$#[S#ML/KECF[S$MLGKECF)s$}$#m#&#j#7R#2Rs%$s$rs$q#j#8H#2Hs%%s$ws$v#j#9S&#2S&s%&s$|s${#j#.I#2Is%'s%%s%$#j#:SE#j#-s%1#j#;s%3##"). Qed.
#[export] Hint Rewrite sym_readB_eqf : bceq.
Lemma know_lookupB_eqf : forall fk segs, know_lookupB segs (mkbc fk) = know_lookup segs fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookup); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookupA); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupAB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupAB_eqf)|] [|@acc; @hints; @sx; @n; @rk; @rb; @kn; @segs; @l; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##f#,#A#$###%#&#'#*#(#)#9#;#8#6#+#5#4#3#=#?#<#0#1#7#@#A#B#C#:#2#/#>(#=$#>(#?$#3,#@&%S&%S'%N%S(k#$#Mk#%%#k#&N#k#'P#k#(Q##CVKD#VLDC#EWKC#DWLCED#FXKE#CDXLEFCD#GYKF#ECDYLFGECD#IZKG#FECDZLGIFECD#J[KI#GFECD[LIJGFECDk#)R5k#*>#k#+>#US#H#OUS$#\DH#JIGFEC&OHOJIGFEC'M$#j#,)#&OHDJIGFEC'M#&j#,s#)#&HJHIGFECDVS)M##HUS$#US*HZS%s#/H(&$#US+&US,HZS%54.%$#\KJ)IGFECD\LJHIGFECD'M$#m#&#j#-s#4#$s#5M?>#j#.s#7#$s#8s#6s#$s###j#/N#$Ns#7s#)s#(#j#0P#$Ps#8s#.s#-#j#1Q#$Qs#9s#3s#2#j#2R#$Rs#:s#8s#7#j#+s#B#j#3s#D##"). Qed.
#[export] Hint Rewrite know_lookupB_eqf : bceq.

Lemma sym_stepB_eq : forall segs i ss scr,
  sym_stepB (mkbc (facts_of (s_know ss))) segs i ss scr = sym_step segs i ss scr.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@LinuxProcessSemantics.Riscv.Instr.instr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sym_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.scripts); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sym_read); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.facts_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_know); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.stepres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SOk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sset); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.shiftl); constr:(@stdpp.bitvector.definitions.bv_signed); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_pc); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.conc_exprB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sr_get); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_regs); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SStop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.decide_branchB); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.enum_branchB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sjump); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sc_dirs); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCBr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sc_reads); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sc_hints); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.to_saddrKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.msize_bytes); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.Riscv.Instr.msize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SSR); constr:(@LinuxProcessSemantics.Riscv.Prelude.bv_eqb); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sr_upd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ridx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_log); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_resv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.resv_inval); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_next); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.flat_scB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.storeok_scB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwKB); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkMdKB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkMdw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.amo_alignedbB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.amo_sz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.amo_sx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr_eqb); constr:(@Corelib.Init.Datatypes.None); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.amo_aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.amo_newvalB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.conc_expr); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.decide_branch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.enum_branch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.to_saddrK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.flat_sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.storeok_sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAluwK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkMdK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.amo_alignedb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.amo_newval); constr:(@LinuxProcessSemantics.Riscv.Instr.awidth); constr:(@LinuxProcessSemantics.Riscv.Instr.branch_cond); constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.decide_branchB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkMdKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkAluwKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.flat_scB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.storeok_scB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.conc_exprB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.enum_branchB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.to_saddrKB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.amo_alignedbB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.amo_newvalB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sym_readB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sym_readB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sym_stepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sym_step)|] [|@sx'; @n; @a; @scr; @x; @z; @op; @b; @sx; @lo; @e; @k; @i0; @t; @dirs'; @sz; @p2; @v; @scs; @p1; @scr'; @p0; @nx'; @r'; @r; @vold; @aop; @i; @rd; @imm; @rs1; @c; @rs2; @rs; @sh; @fm; @pred; @succ; @wd; @aq; @rl; @csr; @uimm; @fmt; @rs3; @rm; @dst; @src; @dir; @o; @old; @s; @l; @ss; @segs|] "#,L#6$P#c#J#&#B#A#$#%#)###(#'#C#D#*#v#E#+#,#=#@#?#;#}#1#-#0#.#9#h$=#Z$'$)$-#5#4$($8$>$@#3#F#Q#^#f#i#k#m#n#l$*$+$,$/$2$4$A$?$9#/$5$;$:$<$7#d$%$&#o#:#S#Y#`#a#_#b#r#q#u#w$1$3$6$B$C$D$E$F$G$H$I$J$K$L$M$N$O$P$Q$R$S#<#K#L#\#W#s$$#j#~#H#G#I#]#>#N#M#X#P#[#R#g#x#z#{#|#O#T#e#p#U#V#t#y$#$.$0U$-&$.'$/%$0%$1)$2&#]&$3&$4&$5$$6$$7&$8$#L*$9)$:%$;$$<$$=$$>$$?%#g&#f&$@%$A&$B$$C$$D%$E$$F%#e&#`&#b'#\&$G%$H$#_%#,%#-&#&$$I$$J$#d'$K&$L$$M$$N$$O%#c'#a&US.SXUS.RVNO#VN#S%VN#S&J#k#$G#k#%S&#k#&S'#k#'S%#,H-#WS<EH#5S=5#5#5#5#5#?#K)5#5#?#@#KKS=5#5#L#VSY'#7-#2.#3#4ML6&$#$MH&#USZR#$#E&,(77#28#3#$MH#*##)E3,K;?#@#K&2#7A#2B#$MH)###2E,L-#6#/L%#HVS1%#4J&#=3#VS[s#.K?s#'@#H&%#US\s#8VS]$#VS>#S^$JE*###s#$LnO#$#(D/#+$#)#$#%C&#*#&#+C&#*#&#+C&#*#&#+C&#*#&#+C'#,#-#%#.C'#,#/#0#%CJG,J-#6#/J%#I%$HM&E$#EGKVS1(&VS1)&M*E$#XS?+E)(nF$G$#(/$#%$#1'##nF$G$#(0)#%$#1(##4PKs#A?#@#H&&#7s#L#2s#M#&)s#?nG#$#1S/K#%#$##:P###s#?JUS@L4S#@-I&$#7s#V#2s#W#&'s#InG#$#1S/H#%#$##:S##/S#%#M%$EXSAHL$#*R#s#MUSBPUSCPWSDK$##+&#nS.$G$#(D4#%#C%#1#2#nF$G$#(DA#%$#16##,P-#6#/P%#H@s#>K8&$#FMnS_#$#3GM#'#E#E#E#S`XLJ%$#4S*&#s#bUS.O?s#rWSa#QSbN$S$#/S*OS$;$#HnG#$##)&#%#%##<S*,S*=S*'.&%$M###KInN%Os$5$#4DH#$%#5#6#nN%s$5S%$#7DH#$%#4#8#nN%s$5S&$#9DK#$%#7#:#nF$s$5$#(D5#%$#9##CJS'=J8s#Ls#J<>$#%@E8B#s#Z%BI+$?#<P*S)$#PP's#Bs#'$s#*#KAs#))s#$9s#**s#%(R$##&#JnF$2$#(D/#%$#;##C3s#+XS2s#\Es#Y#$JI#s#l##s$)L?s$52#K3#XS2s#bEs#_#$JI#s#r##s$/L%s#dKXS2s#fEs#c#$JI#s#v##s$3LXS7s#}S3s#{04L&#s$9$LI%###s$8M2s#6K3#WSEEs#m#$JI#s$$##s$=LXS7s#sEs#p0$JI#s$'##s$@L:Ps#c##s$BJ:L/##s$DMXSFs#zEs#w7$JI#s$.##s$GLWSGEs#z:$JI#s$1##s$JL%s#RKWS4s#T#M8s#U$QQMF#USHMXLJ&$#Ns#OS#s#NOS#;s#N#HnG#$##s#S%#%#s#O##-s#K6#%s#RP8$#QES'#'s#Z(s#Qs#PM###KInN%Os%%$#4DH#$%#5#6#nN%s%%S%$#7DH#$%#4#8#nN%s%%S&$#9DK#$%#7#:#nF$s%%$#(D1#%$#9##CnG#$##D7#%###C,S#-#6#%s#zHWS4$#L=S#,S$-#6#/S$%#I8%#QRK#4S$&#s$sNs#nEs#mOE3Q;+$#nG#$##s#s&#%#,##QJF#%/H+.$#<S$*S)$#PS$UScS''0+%8$#A74*985+(R$##&#S#nG#$##D7#%###CnF$S'$#(D?#%$#<##CnG#$##DA#%###CJSIUSdJ,S+-#6#/S+%#IWS4%#J=S+8'%Q>$#,S--#6#/S-%#E8%#QQPF#USHPXS$S+&$#4S5&#s%CNs$>S-s$=/S5OS-;$#HnG#$##s$C&#%#%##,S5-#6#%)S+8$#QQS*F#%-S$YSJ(S*S#H#+'%#<S5*S)$#'4/#.MP9-+)(RK##%#InN%Os%z$#4DH#$%#=#6#nN%s%zS%$#7DH#$%#4#8#nN%s%zS&$#9DK#$%#7#:#nF$s%z$#(D=#%$#9##CnF$s$G$#(Ds#(#%$#;##CnG#$##Ds#,#%###CnF$s#4$#(Ds#3#%$#>##CnS(#$#?DE#F%#@#As%\%#@#As%V%#@#As%M&#@#B#As%:'#C#B#D#As$h(#3#,#@#E#As$K'#3#B#D#As$:'#*#@#E#As$6'#*#@#E#Fs$0'#*#@#B#Ds$,&#@#E#As$''#*#@#E#Fs#~'#*#@#B#Ds#{(#G#H#I#@#Bs#y&#@#B#As#w#C#C'#*#@#B#Ds#t'#*#@#B#Ds#q(#J#K#L#@#Es#Z)#J#K#L#@#B#Ds#6*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BCGs%Ls%ILs%wLs%sVSe$#VS>s%C#$JEs%J###s%dLnO#$#(D)#+$#)#$#%C&#*#&#+C&#*#&#+C&#*#&#+C&#*#&#+C'#,#-#%#.C'#,#/#0#%CSs%@Es%=s%<Gs%As%>Gs%Bs%>Ss%CE$#XS8s%DEs%As%@nF$G$#(s%G$#%$#1s%?##nF$G$#(s%H(#%$#1s%@##nF$G$#(D##%$#1s%0#s$y)s$ws$ts$s0S$Ps$xJ#s$rs$qnF$s&5$#(D##%$#9s$_#C)s%Ks%Hs$v>s$^#)s$|s$\s%W+#s$ws$[*S)#s$Z's%<s$}#s%$s$YKTs%$&s$zBs%%'s${(R$##&#JnF$s$h$#(D+#%$#;##CCs%VEs%Rs$X$JI#s%e##s%~LCs%YEs%Us$U$JI#s%h##s&%LCs%\Es%Xs$T$JI#s%k##s&(LXS0s%sS3s%ps$a$LI#s$R##s&+MXS0s%bEs%^s$Z$JI#s%q##s&.LXS9s%eEs%as$]$JI#s%t##s&1LDs%;s$EM)s%<s$FQ0S$Ps%=J#s$Cs$B)s$=s$;QES'#'s%6s$@s%-s%,M###KInN%Os&]$#4DH#$%#5#6#nN%s&]S%$#7DH#$%#4#8#nN%s&]S&$#9DK#$%#7#:#nF$s&]$#(D*#%$#9##CnG#$##D-#%###CDs$9s$7L)s$4s$1QRK#+$s$(s$'*S)#s$&'s$1s$,#s$9s$%s$$Ts$9's$+Bs$:(s$,(R$##&#S#nG#$##D*#%###CnF$S'$#(Ds$@#%$#<##CnG#$##D.#%###CDs#|s#yJ)s#}s#zQ>s#y#)s#vs#sQ0S,S-s#wS+#s#qs#p)s#gs#eQYS:s#hS*S#Hs#b+$s#d#*S)#s#a's#rs#m#s#lMPBs#l's#g(RK##%#InN%Os&|$#4DH#$%#=#6#nN%s&|S%$#7DH#$%#4#8#nN%s&|S&$#9DK#$%#7#:#nF$s&|$#(D.#%$#9##CnF$s%I$#(D1#%$#;##CnG#$##D4#%###CnF$s$6$#(Ds$5#%$#>##CnS(#$#?DE#F%#@#As&^%#@#As&X%#@#As&O&#@#B#As#X'#C#B#D#As#P(#3#,#@#E#As#M'#3#B#D#As#B'#*#@#E#As#?'#*#@#E#Fs#<'#*#@#B#Ds#9&#@#E#As#6'#*#@#E#Fs%$'#*#@#B#Ds#3(#G#H#I#@#Bs${&#@#B#As$y#C#C'#*#@#B#Ds#0'#*#@#B#Ds$s(#J#K#L#@#Es#$)#J#K#L#@#B#D7*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.Ds#a#j#Us&}#k#SOOk#VO#k#>s$<#k#JSK#US:s'$0S$Ps%pJs%ks%js%inF$s'-$#(D##%$#9s%W#C0S$Ps%rJs$zs$xs$wnF$s'/$#(D##%$#9s$i#CnG#$##Ds$}#%###C0S,S-s$8S+s$4s$2s$1XS;S*S#Hs#~+s$&s$$#*S)#s#}'s$2s$-#s$,MP##s#{InN%Os':$#4DH#$%#=#6#nN%s':S%$#7DH#$%#4#8#nN%s':S&$#9DK#$%#7#:#nF$s':$#(D+#%$#9##CnF$s%c$#(Ds$D#%$#;##CnG#$##Ds$H#%###CnF$s$P$#(Ds$O#%$#>##CnS(#$#?DE#F%#@#As&x%#@#As&r%#@#As&i&#@#B#As&V'#C#B#D#As&((#3#,#@#E#A3'#3#B#D#As%V'#*#@#E#As%R'#*#@#E#Fs%L'#*#@#B#Ds%H&#@#E#As%C'#*#@#E#Fs%>'#*#@#B#Ds%;(#G#H#I#@#Bs%9&#@#B#As%7#C#C'#*#@#B#Ds%4'#*#@#B#Ds%1(#J#K#L#@#E0)#J#K#L#@#B#Ds$R*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#=j#.8#k#JSKGk#.O#USLs'<Hs%6MnG#$##D##%#8#CVJs$zLnG#$##D##%#s$\#CVS#s$UJ+s$<s$:s#5*S)#s$7's$Hs$C#s$BMP##s$5InN%Os'P$#4DH#$%#=#6#nN%s'PS%$#7DH#$%#4#8#nN%s'PS&$#9DK#$%#7#:#nF$s'P$#(DA#%$#9##CnF$s%y$#(Ds$Z#%$#;##CnG#$##D,#%###CnF$s$f$#(Ds$e#%$#>##CnS(#$#?DE#F%#@#As'2%#@#As',%#@#As'#&#@#B#As&l'#C#B#D#As&>(#3#,#@#E#As#)'#3#B#D#As%l'#*#@#E#As%h'#*#@#E#Fs%b'#*#@#B#Ds%^&#@#E#As%Y'#*#@#E#Fs%T'#*#@#B#Ds%Q(#G#H#I#@#Bs%O&#@#B#As%M#C#C'#*#@#B#Ds%J'#*#@#B#Ds%G(#J#K#L#@#E1)#J#K#L#@#B#D/*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s#3j#+6#k#AS/S'k#.O#USMs'RHs&?s&>0S$Ps&CJ#s&=s&<nF$s'\$#(D##%$#9s&*#CVMs&os&A>s&)#Hs&'s&~+#s&Bs&&*S)#s&%'s&cs&H#s&Ks&$KAs&J&s&E9s&K's&F(R$##&#JnF$s&3$#(D+#%$#;##CHs%ZQ0S$Ps&QJ#s%Ws%VVSNs%OQES'#'s&Js%Ts&As&@M###KInN%Os'q$#4DH#$%#5#6#nN%s'qS%$#7DH#$%#4#8#nN%s'qS&$#9DK#$%#7#:#nF$s'q$#(D*#%$#9##CnG#$##Ds#}#%###CVPs%DQRK#+$s%;s%:*S)#s%9's%Ds%?#s%Ls%8s%7As%K's%>9s%L(s%?(R$##&#S#nG#$##D*#%###CnF$S'$#(Ds%S#%$#<##CnG#$##Ds#}#%###CVS#s%0Q>s%/#VS$s%)Q0S,S-s%-S+#s%'s%&VS;s$wQ+#s$us#p*S)#s$r's%'s$~#s$}MP9s$|&s$x(RK##%#InN%Os(1$#4DH#$%#=#6#nN%s(1S%$#7DH#$%#4#8#nN%s(1S&$#9DK#$%#7#:#nF$s(1$#(D-#%$#9##CnF$s&Z$#(D0#%$#;##CnG#$##Ds$%#%###CnF$s%G$#(Ds%F#%$#>##CnS(#$#?DE#F%#@#As'o%#@#As'i%#@#As'`&#@#B#As'M'#C#B#D#As&{(#3#,#@#E#As#7'#3#B#D#As#,'#*#@#E#As&I'#*#@#E#Fs&C'#*#@#B#Ds&?&#@#E#As&:'#*#@#E#Fs&5'#*#@#B#Ds&2(#G#H#I#@#Bs&0&#@#B#As&.#C#C'#*#@#B#Ds&+'#*#@#B#Ds&((#J#K#L#@#EA)#J#K#L#@#B#D5*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s#pj#Ws#=#k#+Os'Ok#&O#k#CSf#US8s(4IEs'Ns'MnF$G$#(s'Ts'I#%$#1s'L##nF$G$#(s'Us'N#%$#1s'M##nF$G$#(D##%$#1s'=#s'*As''s$fs&~9s'(s$gs'#(R$##s$f#JnF$s&l$#(Ds$k#%$#;##CAs%ts$Cs%g9s%us$Ds%h(R$##s$B#S#nG#$##Ds$F#%###CnF$S'$#(Ds%|#%$#<##CnG#$##Ds$J#%###C9s%As$9s%=(RK##s$7#InN%Os(R$#4DH#$%#=#6#nN%s(RS%$#7DH#$%#4#8#nN%s(RS&$#9DK#$%#7#:#nF$s(R$#(Ds$@#%$#9##CnF$s&{$#(Ds$C#%$#;##CnG#$##Ds$F#%###CnF$s%h$#(Ds%g#%$#>##CnS(#$#?DE#F%#@#As(4%#@#As(.%#@#As(%&#@#B#As'n'#C#B#D#A9(#3#,#@#E#As%#'#3#B#D#A4'#*#@#E#As&j'#*#@#E#Fs&d'#*#@#B#Ds&`&#@#E#As&['#*#@#E#Fs&V'#*#@#B#Ds&S(#G#H#I#@#Bs&Q&#@#B#As&O#C#C'#*#@#B#Ds&L'#*#@#B#Ds&I(#J#K#L#@#Es$V)#J#K#L#@#B#D-*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s$5j#U@#k#.OOUSOs(SUEs(%nO#$#(D##+$#)s'u$#%C&#*#&#+C&#*#&#+C&#*#&#+C&#*#&#+C'#,#-#%#.C'#,#/#0#%CUMs'oUMs'oMs'sE$#nF$G$#(s'w##%$#1s'o#s%3nF$G$#(s'xs'q#%$#1s'p##nF$G$#(D##%$#1s'`#s'MnS(#$#?DE#F%#@#As(A%#@#As(;%#@#As(2&#@#B#A)'#C#B#D#A#(#3#,#@#E#As%0'#3#B#D#AA'#*#@#E#As&w'#*#@#E#Fs&q'#*#@#B#Ds&m&#@#E#As&h'#*#@#E#Fs&c'#*#@#B#Ds&`(#G#H#I#@#Bs&^&#@#B#As&\#C#C'#*#@#B#Ds&Y'#*#@#B#Ds&V(#J#K#L#@#Es$c)#J#K#L#@#B#D:*#*#J#K#L#@#B#D0'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s$Bj#..#k#%S&s(ik#&S'#USPs(anO#$#(Ds%H#+$#)s(&$#%C&#*#&#+C&#*#&#+C&#*#&#+C&#*#&#+C'#,#-#%#.C'#,#/#0#%CMs'~Es%@s%?nF$G$#(s(&##%$#1s'z#s%>nF$G$#(s('s'|#%$#1s'{##nF$G$#(D##%$#1s'k#s'XHs%8s'P(Rs#1##s%7#JnF$s'=$#(Ds%<#%$#;##CVPs$ps&8(Rs#0##s$n#S#nG#$##Ds$r#%###CnF$S'$#(Ds&L#%$#<##CnG#$##Ds$v#%###CVS;s$es%i(RK##s$c#InN%Os(~$#4DH#$%#=#6#nN%s(~S%$#7DH#$%#4#8#nN%s(~S&$#9DK#$%#7#:#nF$s(~$#(Ds$l#%$#9##CnF$s'K$#(Ds$o#%$#;##CnG#$##Ds$r#%###CnF$s&8$#(Ds&7#%$#>##CnS(#$#?DE#F%#@#As(`%#@#As(Z%#@#As(Q&#@#B#A;'#C#B#D#A7(#3#,#@#E#As%O'#3#B#D#A3'#*#@#E#As':'#*#@#E#Fs'4'#*#@#B#Ds'0&#@#E#As'+'#*#@#E#Fs'&'#*#@#B#Ds'#(#G#H#I#@#Bs&}&#@#B#As&{#C#C'#*#@#B#Ds&x'#*#@#B#Ds&u(#J#K#L#@#Es%&)#J#K#L#@#B#D-*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s$aj#X?#USQs(~(R:s%K#s%N#JnF$s'T$#(Ds%S#%$#;##C(R9s%%#s%(#S#nG#$##Ds%,#%###CnF$S'$#(Ds&b#%$#<##CnG#$##Ds%0#%###CnS(#$#?DE#F%#@#As(l%#@#As(f%#@#As(]&#@#B#As#''#C#B#D#As##(#3#,#@#E#As%['#3#B#D#A('#*#@#E#As'F'#*#@#E#Fs'@'#*#@#B#Ds'<&#@#E#As'7'#*#@#E#Fs'2'#*#@#B#Ds'/(#G#H#I#@#Bs'-&#@#B#As'+#C#C'#*#@#B#Ds'('#*#@#B#Ds'%(#J#K#L#@#Es%2)#J#K#L#@#B#D#*#*#J#K#L#@#B#Ds$m'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s$mj#Xs#+#k#+OOk#&O#k#*SI#US0s)1WES3s(_s'P$LI#s'A##s(vMIEs(Ms'I$JI#s(`##s(yLnS(#$#?DE#F%#@#As(y%#@#As(s%#@#As(j&#@#B#As#4'#C#B#D#As#0(#3#,#@#E#As%h'#3#B#D#As%]'#*#@#E#As'S'#*#@#E#Fs'M'#*#@#B#Ds'I&#@#E#A&'#*#@#E#Fs'?'#*#@#B#D#(#G#H#I#@#Bs':&#@#B#As'8#C#C'#*#@#B#Ds'5'#*#@#B#Ds'2(#J#K#L#@#Es%?)#J#K#L#@#B#Ds%2*#*#J#K#L#@#B#Ds$z'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s$zj#.,#k#*Sg.US9s)<nS(#$#?DE#F%#@#As(~%#@#As(x%#@#As(o&#@#B#As#9'#C#B#D#As#5(#3#,#@#E#As%m'#3#B#D#As%b'#*#@#E#As'X'#*#@#E#Fs'R'#*#@#B#Ds'N&#@#E#As%V'#*#@#E#Fs'D'#*#@#B#Ds%S(#G#H#I#@#Bs'?&#@#B#As'=#C#C'#*#@#B#D('#*#@#B#Ds'7(#J#K#L#@#Es%D)#J#K#L#@#B#Ds%7*#*#J#K#L#@#B#Ds%#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s%#j#.&#USRs)@IEs(Ys'_$JI#s(l##s))LIEs(\s'\$JI#s(o##s),LnS(#$#?DE#F%#@#As),%#@#As)&%#@#As(y&#@#B#As#C'#C#B#D#As#?(#3#,#@#E#As%w'#3#B#D#As%l'#*#@#E#A&'#*#@#E#F#'#*#@#B#D2&#@#E#As%`'#*#@#E#Fs'N'#*#@#B#Ds%](#G#H#I#@#Bs'I&#@#B#As'G#C#C'#*#@#B#Ds%Z'#*#@#B#Ds'A(#J#K#L#@#Es%N)#J#K#L#@#B#Ds%A*#*#J#K#L#@#B#Ds%-'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s%-j#.;#USSs)JIEs&(s&'nF$G$#(s(j##%$#1s(b#s&&nF$G$#(s(ks#v#%$#1s(c##nF$G$#(D##%$#1s(S#s(@nS(#$#?DE#F%#@#As)4%#@#As).%#@#As)%&#@#B#As#K'#C#B#D#A#(#3#,#@#E#As&#'#3#B#D#As%t'#*#@#E#As%q'#*#@#E#Fs%n'#*#@#B#Ds%k&#@#E#As%h'#*#@#E#Fs'V'#*#@#B#Ds%e(#G#H#I#@#Bs'Q&#@#B#As'O#C#C'#*#@#B#Ds%b'#*#@#B#Ds'I(#J#K#L#@#Es%V)#J#K#L#@#B#Ds%I*#*#J#K#L#@#B#Ds%5'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BC.D#s%5j#Us#|#4E&#s)<$EHs)?###s);I&s)D&7s)O#2s)P#3#$EH#)##s)AI3+&-s)87s)V#2s)W#$EH&###s)GI,M-#/M%#HG%#3s'u$LE#s&J##s)OMnO#$#(D&#+$#)#$#%C&#*#&#+C&#*#&#+C&#*#&#+C&#*#&#+C'#,#-#%#.C'#,#/#0#%C%s)=ISs)@E#s)=Gs)A$Ss)BE#s&TXS8s)CE&s)@nF$G$#(s)2$#%$#1s)*##nF$G$#(s)3'#%$#1s)+##&s)As(~7s)k#2s)l#nG#$#1S/K#%###s)C:J###s)]LUS@M&s),s({7s)r#2s)s#nG#$#1S/H#%###s)(:P#%s(kMXSAHL#s(N*R#s)fUSBJUSCJWSDK$##)&#nS.$G$#(D/#%#C%#1#2#nF$G$#(D7#%$#11##)s)Gs)Cs(r0S#Js)HL#s(qs(p4S,&#s)s/S,;#s(kHnG#$##s(qs(n#%#$##<S,,S,=S,')&%$M###KInN%Os*A$#4DH#$%#5#6#nN%s*AS%$#7DH#$%#4#8#nN%s*AS&$#9DK#$%#7#:#nF$s*A$#(D0#%$#9##C=L)s)ls#/s)'>$#%s)XE)s)[#s)e+#s))s)Y<J*S)$#PJ's)ns)^$s)a#KTs)a(s).Bs)b)s)/(R$##&#LnF$s(x$#(D.#%$#;##CCs)zEs)ws(h$LI#s(Y##s*2MCs)}Es)zs(e$LI#s(\##s*5M%s)~KCs*%Es)~#$LI#s(`##s*9MXS0s#OS3s#Ms(r$MI#s*=##s*<EWSEEs*(s(a$LI#s(f##s*?MXS0s*.Es*+,$LI#s(i##s*BM:Js*+##s*DL:Ms*G##s*FEXS9s*5Es*23$LI#s(p##s*IMWSGEs*56$LI#s(s##s*LMDs*'s({M)s*(s(|Q0S#Js*)L#s(^s(];s#=s([HnG#$##s)Os(]#%#s#>##-s#;%s#@P)$#QES'#'s#D's#@s#?M###KInN%Os*|$#4DH#$%#5#6#nN%s*|S%$#7DH#$%#4#8#nN%s*|S&$#9DK#$%#7#:#nF$s*|$#(D.#%$#9##CnG#$##D1#%###CDs)fs)cL=P%s)tI)s([#QRK#;s)ws(Ns(MnG#$##s)as(P#%#s)x##+&s(Ks(]<S#*S)$#PS#'s*$'$s(d#s(ITs(d+s(PBs(e,s(Q(R$##&#PnG#$##D.#%###CnF$S'$#(D2#%$#<##CnG#$##D4#%###CDs(es(bJ=S$>#s'5%s(FE)s(I#Q0SNS+s(JS$#s(;s(:4S6&#s*z/S6;#s(8HnG#$##s)xs(;#%#$##,S6-#%'S+)$#Q%)S$YS:&S*S#H#+%s(7#<S6*S)$#'/,#+MPB+)s(;(RK##%#InN%Os+P$#4DH#$%#=#6#nN%s+PS%$#7DH#$%#4#8#nN%s+PS&$#9DK#$%#7#:#nF$s+P$#(D8#%$#9##CnF$s)y$#(D<#%$#;##CnG#$##D?#%###CnF$s(f$#(Ds(e#%$#>##CnS(#$#?DI#F%#@#As$V%#@#As$P%#@#As$J&#@#B#As$A'#C#B#D#As$%(#3#,#@#E#As#q'#3#B#D#As#b'#*#@#E#As#_'#*#@#E#Fs#\'#*#@#B#Ds#X&#@#E#As#U'#*#@#E#Fs#R'#*#@#B#Ds#O(#G#H#I#@#Bs#M&#@#B#As#K#C#C'#*#@#B#Ds#H'#*#@#B#Ds#E(#J#K#L#@#Es#5)#J#K#L#@#B#DB*#*#J#K#L#@#B#D#'#*#@#B#MC'#*#@#N#MC'#O#@#B#AC'#O#B#D#AC*#*#O#@#B#D#P#QC)#*#O#@#B#D#QC'#O#@#B#QC(#*#O#@#B#DC(#*#O#@#B#DC(#*#O#@#B#DC(#R#S#@#B#QC'#T#O#@#BC&#O#@#BCVShD#6s+OUST#USis+Q1s%}s$fs$_&$#US2&USjs+T1s%'s$ss$j%$#USF)USks+W1s${s$zs$w%$#US7,USls+Z1s%-s%,s%#%$#USU/USms+]1s%\s%>s%3%$#USV2USns+`1s%_s%^s%B%$#US15USos+c1s%ps%os%d%$#US?8USps+f1s&6s&5s%t%$#USW;USqs+i1s&ws&vs&<%$#US4>USrs+l1s'4s'3s&|%$#USJAUSss+o1s'Os'Ns'9%$#WStEHs#$WSus+rEH1s+us+rs'V%$#YSvs#'EIHKXSwEIHK.D$#m#&#j#'S%#j#YSx#j#?S(#j#Zs,*##"). Qed.
(* [comment removed for export] *)
Lemma sym_step_know : forall segs i ss scr ss' scs scr',
  sym_step segs i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros segs i ss scr ss' scs scr' H. unfold sym_step, sym_read in H.
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try reflexivity.
Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Local Open Scope lzb_scope.
Definition zf_coversB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod two64)%Z with RInside _ => true | _ => false end
   | _ => false
   end) || xinsideB bc rb rk (elen n) kb kk len.
Local Close Scope lzb_scope.

Definition kentry_overlayB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      zf_coversB bc rb rk n kb kk len
  | _ => false
  end.

Definition kentry_readableB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlayB bc rb rk n K
  end.

Local Open Scope lzb_scope.
Definition kn_readableB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsbL (kentry_readableB bc rb rk n) kn || know_bytes_cov segs true kn rb rk n.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition kn_overlayB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsbL (kentry_overlayB bc rb rk n) kn || know_bytes_cov segs false kn rb rk n.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition x_dischargeableB (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlay segs (bc_fk bc) kn (a_base a) (a_off a) n
  | _ => false
  end%lzb.
Local Close Scope lzb_scope.

Definition x_filterB (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          (* [comment removed for export] *)
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeableB bc ss ss' rb sc)) scs
  end.

Definition sym_stepXB (bc : bctx) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepB bc segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.


Lemma zf_coversB_eqf : forall fk, zf_coversB (mkbc fk) = zf_covers fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.zf_coversB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zf_covers); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rel_lit); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rangerel); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf)|] [|@len; @kk; @kb; @n; @rk; @n2; @k2; @b2; @n1; @k1; @b1; @x; @delta; @l0; @n0; @op; @a; @b; @sx; @lo; @e; @k; @i; @x4; @x3; @x2; @x1; @x0; @fk|] "##x#+#H#A###$#1#%#&#4#'#)#(#2#5#7#3#9#*#B#@#=#>#C#E#:#.#/#?#G#D#H#I#J#8#6#F#0#<#;(#C$#D$#E(#F)#G%US*S+k#$FIk#%M#k#&F#k#'P#k#(M##DUN#UOD#EVN#DVOED#GWN#EDWOGED#HXN#GEDXOHGED#JYN#HGEDYOJHGED#LZN#JHGEDZOLJHGEDk#)FIk#*M#k#+F#k#,F#k#-M#k#.F#UQKUS%LVS&DS,&RK$JH#nS##$#/I##'$#0S$#C#C#CnF#$#$IE#+$#1#$#2C&#3#4#5C&#3#4#5C&#3#4#5C&#3#4#5C'#6#7#2#8C'#6#9#:#2CUS'JZDKL#HGE'%#$S-US(#$$$#$#$#$#US(#VS.)#VS&D#&RK4JH#nS##$#/I##'$#0S$#C#C#CnF#$#$IE#+$#1#$#2C&#3#4#5C&#3#4#5C&#3#4#5C&#3#4#5C'#6#7#2#8C'#6#9#:#2C[QRKL2HGE'$#WS)I2#j#5<#US%J&KL#HG+nS##$#/I##'$#0S$#C#C#CnF#$#$ID#+$#1#$#2C&#3#4#5C&#3#4#5C&#3#4#5C&#3#4#5C'#6#7#2#8C'#6#9#:#2CUS'H[QKLJ#GED'%#VS/I##KUS0#US1KZS2s#(s#'.&$#[N&LJHGED[OKLJHGEDWS)I$#m#&#j#;F#%FIs#5s#4#j#<M#%Ms#Ls#:s#9#j#=F#%Fs#Ms#?s#>#j#>P#%Ps#Ns#Ds#C#j#?M#%Ms#Os#Is#H#j#/F#%Fs#Ps#Ns#M#j#@s#V##"). Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : forall fk, kentry_overlayB (mkbc fk) = kentry_overlay fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_overlayB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry_overlay); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zf_covers); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.zf_coversB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.zf_coversB_eqf)|] [|@K; @n; @rk; @len; @kk; @kb; @rb; @a; @w; @v; @k; @lo; @hi; @e; @m; @n0; @a1; @n1; @a2; @n2; @c; @b; @x2; @x1; @x0; @x; @fk|] "##]#.#@#$#>###7#%#2#&#+#*#?#5#8#:#4#'#6#)#,#<#(#=#1#-#@#A#B#;#9#3&#>$#5*#?(US(Hk#$HFk#%R#k#&M##EUN#UOE#CVN#EVOCE#GWN#CEWOGCE#IXN#GCEXOIGCEk#'PFk#(M#k#)P#k#%R#k#&M#k#*P#US%QZQJKS#CEGnL#$#+FC#$%#)#(#ZS&S$JKCEInL#$#+FG#$%#)#(#nH#$#$FC#-&#+#,#-D%#+#'%&#+#'#.#%#/#0D%#1#2D&#1#/#0D%#+#3D'#4#5#6#7D&#+#'#8#%#+#'%$S$JKS#CEGnL#$#+FC#$%#)#(#$S)S$JKCEInL#$#+FG#$%#)#(#nH#$#$FC#-&#+#,#-D%#+#'%&#+#'#.#%#/#0D%#1#2D&#1#/#0D%#+#3D'#4#5#6#7D&#+#'#8#%#+#'%WS'F(#j#9/#$JKS#S&CEGnL#$#+FC#$%#)#(#$S$JKS#CEInL#$#+FG#$%#)#(#nH#$#$FE#-&#+#,#-D%#+#'%&#+#'#.#%#/#0D%#1#2D&#1#/#0D%#+#3D'#4#5#6#7D&#+#'#8#%#+#'%VS*F##QUS+#US,QZS-98,&$#YN&IGCEYOQIGCEWS'F$#m#&#j#:H#%HFs#&s#%#j#;R#%Rs#5s#+s#*#j#<M#%Ms#6s#0s#/#j#=P#%Ps#7s#5s#4#j#>s#;##"). Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kentry_readableB_eqf : forall fk, kentry_readableB (mkbc fk) = kentry_readable fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_readableB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry_readable); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry_overlay); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rel_lit); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.rangerel); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_overlayB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_overlayB_eqf)|] [|@K; @n; @rk; @rb; @x; @delta; @a; @kb; @kk; @w; @v; @n0; @k; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @b; @x2; @x1; @x0; @fk|] "##\#-#C###6#$#%#'#&#)#1#*#(#@#7#9#+#5#4#3#;#=#,#A#?#B#<#0#C#D#E#:#8#2#>'#@$#4(#A(#B$US+Jk#$JDk#%Q#k#&R##CUN#UOC#EVN#CVOEC#FWN#ECWOFEC#HXN#FECXOHFECk#'S#/US$G&K&HZS%S&P$EC#nS'#$#(D##'$#)S(#M#M#MnS)#$#*DF#$%#+#,#XFILGHXHKILGXGPKILnJ#$#$DE#-&#*#-#.&%#*#/%&#*#/#0$%#1#2%%#3#4%&#3#1#2$%#*#/%'#5#6#7#8#&#*#/#9$%#*#/%$KILGH$PKILG$S&PKILnJ#$#$DE#-&#*#-#.*%#*#/%&#*#/#0$%#1#2%%#3#4%&#3#1#2$%#*#/%'#5#6#7#8#&#*#/#9$%#*#/%WS*D'#j#:2#&IZS%PK#EC1nS'#$#(D##'$#)S(#M#M#MnS)#$#*DF#$%#+#,#$ILGHFnJ#$#$DC#-&#*#-#.$%#*#/#&#*#/#0-%#1#2#%#3#4#&#3#1#2-%#*#/#'#5#6#7#8,&#*#/#9-%#*#/#VS,D##GUS-#US.GZS/=<-&$#YN&HFECYOGHFECWS*D$#m#&#j#;J#%JDs#%s#$#j#<Q#%Qs#4s#*s#)#j#=R#%Rs#5s#/s#.#j#(S##%S#s#6s#4s#3#j#>s#:##"). Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : forall fk, kn_readableB (mkbc fk) = kn_readable segs fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kn_readableB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kn_readable); constr:(segs); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry_readable); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.existsbL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_bytes_cov); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.Lists.List.existsb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_readableB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_readableB_eqf)|] [|@n; @rk; @rb; @K; @b; @x2; @x1; @x0; @x; @fk|] "##W#)#?###$#%#&#'#6#2#-#3#5#1#0#/#8#<#=#>#9#,#;#(#?#@#A#7#4#.#:&#<$#=(#>%US%Jk#$MIk#%N#k#&O##CUK#VLHC#DVK#CWLHDC#EWK#DCXLHEDC#FXK#EDCYLHFEDCk#'JIk#$M#k#%N#k#&O#UPGWCFEDWS&J#GZQHRGFED%$#XPS'FEDWS#J#G%#&WS$I&#j#(,#XPGEDCWS#J#FZQHRFEDC%$#VS(I##GUS)#US*GZS+54+&$#YK&FEDCZLHGFEDCWS$I$#m#&#j#)M#$MI@?#j#*N#$Ns#/s#%s#$#j#+O#$Os#0s#*s#)#j#,s#3#$s#4s#1s#/s#.#j#-s#5##"). Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : forall fk, kn_overlayB (mkbc fk) = kn_overlay segs fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kn_overlayB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kn_overlay); constr:(segs); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry_overlay); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.existsbL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_bytes_cov); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.Lists.List.existsb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_overlayB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.kentry_overlayB_eqf)|] [|@n; @rk; @rb; @K; @b; @x2; @x1; @x0; @x; @fk|] "##W#)#?###$#%#&#'#6#2#-#3#5#1#0#/#8#<#=#>#9#,#;#(#?#@#A#7#4#.#:&#<$#=(#>%US%Jk#$MIk#%N#k#&O##CUK#VLHC#DVK#CWLHDC#EWK#DCXLHEDC#FXK#EDCYLHFEDCk#'JIk#$M#k#%N#k#&O#UPGWCFEDWS&J#GZQHRGFED%$#XPS'FEDWS#J#G%#&WS$I&#j#(,#XPGEDCWS#J#FZQHRFEDC%$#VS(I##GUS)#US*GZS+54+&$#YK&FEDCZLHGFEDCWS$I$#m#&#j#)M#$MI@?#j#*N#$Ns#/s#%s#$#j#+O#$Os#0s#*s#)#j#,s#3#$s#4s#1s#/s#.#j#-s#5##"). Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.

Lemma x_dischargeableB_eq : forall ss ss' rb sc,
  x_dischargeableB (mkbc (facts_of (s_know ss))) ss ss' rb sc = x_dischargeable segs ss ss' rb sc.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sym_state); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.facts_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_know); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kn_readable); constr:(segs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Stdlib.Arith.PeanoNat.Nat.leb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kn_overlay); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr_eqb); constr:(@Stdlib.Arith.PeanoNat.Nat.eqb); constr:(@Stdlib.Bool.Bool.eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.s_next); constr:(@Stdlib.Arith.PeanoNat.Nat.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.evars_lt); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.WithSegs.x_dischargeableB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.x_dischargeable)|] [|@n; @z; @n0; @op; @a0; @b; @sx; @lo; @e; @k; @i; @p0; @a'; @n'; @p; @sx'; @rb; @j; @sx0; @e0; @sc; @taken; @c; @a; @a1; @n1; @a2; @n2; @l; @ss'; @ss|] "#$E#-#V#=#5###C#&#$#2#%#G#*#1#6#3#4#,#+#?#@#>#)#P#'#Q#(#<#0#8#9#F#J#L#N#S#U#T#V#7#W#X#R#I#;#:#B#H#A#D#E#K#M#O/#J%#K$#L$#M$#N)#O%#P$#Q$#R$#S)#T%#U$VIOPVI#DUM#US-S.%G&#US#S$VS%#E)S$)#)#US##VS%E#nD#$##D(#%###C%L*J+JUS/E'FG&%$#nD#$##D(#%###CnK#$#$DE#+$#%#$#&C&#'#(#)C&#'#(#)C&#'#(#)C&#'#(#)C'#*#+#&#,C'#*#-#.#&C$S0(#E$$$#$#$#$#$#$#(E#nD#$##D+#%###C%S&*H+H,FJ%$#EnD#$##D'#%###CVS1HQ-ERnD#$##D$#%###CVS2JLnD#$##D$#%###CnI%OP$#/DH#$%#0#1#nI%s#-D$#2DE#$%#/#3#nM$s#-$#4DL#%$#2##C.Q-E#nD#$##D%#%###C.RVS'E#nD#$##D%#%###C*S(VS))#nD#$##D%#%###C(s##GnD#$##D$#%###C(G=nD#$##D$#%###C%Q+S('FS*$+#GnD#$##D&#%###CnK#$#,DE#+$#%C$#5#&#'#(#)C&#'#(#)C&#'#(#)C&#'#(#)C'#6#+#&#7C'#6#-#.#&CnN#$#8DH#*'#9#:#;#)C%#;#$s#-'#<#=#>#?C'#<#=#>#?C%#;#$='#;#$#*#,#%#;#)C#s#;s#6&s#5'F#s#6s#5s#4s#3#%#nK#$#$DE#+$#%#$#&C&#'#(#)C&#'#(#)C&#'#(#)C&#'#(#)C'#*#+#&#,C'#*#-#.#&C#s#1s#)&s#(,F#s#)s#(s#'E#%##s#&s#%##s#$nI%OP$#/DH#$%#0#1#nI%s#ND$#2DE#$%#/#3#nM$s#N$#4DL#%$#2##C##B##@##>##=##<&;'F#<s##;G#%#nK#$#,DE#+$#%C$#5#&#'#(#)C&#'#(#)C&#'#(#)C&#'#(#)C'#6#+#&#7C'#6#-#.#&CnN#$#8DH#*'#9#:#;#)C%#;#$5'#<#=#>#?C'#<#=#>#?C%#;#$1'#;#$#*#,#%#;#)CWS+D;#j#@s#X#'F6s#<s#Ms#Ls#K#=#nK#$#$DE#+$#%#$#&C&#'#(#)C&#'#(#)C&#'#(#)C&#'#(#)C'#*#+#&#,C'#*#-#.#&C%S*&#,F#$s#@s#?E#=#nM$s#b$#4DS&#%$#27#C-Es#4#$#.LVS'E##%#VS)s#9s#6#$###s#5##s#4%R&#'F#$s#<s#4G#&#nK#$#,DE#+$#%C$#5#&#'#(#)C&#'#(#)C&#'#(#)C&#'#(#)C'#6#+#&#7C'#6#-#.#&CnN#$#8DE#*'#9#:#;#)C%#;#$6'#<#=#>#?C'#<#=#>#?C%#;#$2'#;#$#*#,#%#;#)CVS3D#US4s#oUS5#US6s#qZS7s#ts#r>&$#YS8&GJHEYS9FGJHEWS+D$#m#&#j#8N#j#4s#{#j#AS,#j#BS,##"). Qed.
Lemma x_filterB_eq : forall ss ss' scs,
  x_filterB (mkbc (facts_of (s_know ss))) ss ss' scs = x_filter segs ss ss' scs.
Proof.
  intros. unfold x_filterB, x_filter. destruct scs as [|sc rest]; [reflexivity|].
  erewrite filter_ext; [reflexivity|]. intros x. rewrite x_dischargeableB_eq. reflexivity.
Qed.
Lemma cap_rd_know : forall K i ss, s_know (cap_rd K i ss) = s_know ss.
Proof.
  intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
  destruct (bv_eqb rd 0); [reflexivity|]. destruct (esize_le (sr_get (s_regs ss) rd) (S K)); reflexivity.
Qed.
Lemma sym_stepXB_eq : forall K i ss scr,
  sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXB, sym_stepX. rewrite sym_stepB_eq.
  destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [|reflexivity]. rewrite x_filterB_eq. reflexivity.
Qed.
Lemma sym_stepX_know : forall K i ss scr ss' scs scr',
  sym_stepX segs K i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros K i ss scr ss' scs scr' H. unfold sym_stepX in H.
  destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_know. exact (sym_step_know _ _ _ _ _ _ _ E).
Qed.

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Fixpoint sym_execTXB_go (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%lzb then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXB bc K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXB_go bc t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Local Close Scope lzb_scope.
Definition sym_execTXB (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXB_go bc t K fuel first stops (clr ss) (clr ss).

Lemma sym_execTXB_go_eq : forall t K fuel first stops ss ck,
  sym_execTXB_go (mkbc (facts_of (s_know ss))) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXB_go sym_execTX_go].
  change (if negb first then existsb (Z.eqb (s_pc ss)) stops else false) with (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool in *; destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXB_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXB_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXB (mkbc (facts_of kn0)) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXB, sym_execTX.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXB_go_eq.
Qed.
(* [comment removed for export] *)
Lemma sym_execTX_go_know : forall t K fuel first stops ss ck,
  s_know ck = s_know ss ->
  s_know (sym_execTX_go segs t K fuel first stops ss ck) = s_know ss.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck Hck.
  - cbn. destruct (s_clean ss); [reflexivity|exact Hck].
  - cbn [sym_execTX_go].
    change (if negb first then existsb (Z.eqb (s_pc ss)) stops else false) with (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool in *; destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); [reflexivity|exact Hck]|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    destruct scs; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    pose proof (sym_stepX_know _ _ _ _ _ _ _ E) as HK.
    rewrite IH; [exact HK|]. destruct (s_clean ss'); [reflexivity|]. rewrite Hck, HK. reflexivity.
Qed.
Lemma sym_execTX_know : forall t K fuel first stops ss,
  s_know (sym_execTX segs t K fuel first stops ss) = s_know ss.
Proof.
  intros. unfold sym_execTX. rewrite sym_execTX_go_know; [|reflexivity]. destruct ss; reflexivity.
Qed.
(* [comment removed for export] *)
Definition sym_stepXBI (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBI bc kx segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Lemma sym_stepXBI_eq : forall K i ss scr,
  sym_stepXBI (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXBI. rewrite sym_stepBI_eq. fold (sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr). apply sym_stepXB_eq.
Qed.
Local Open Scope lzb_scope.
Fixpoint sym_execTXBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%lzb then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI bc kx K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Local Close Scope lzb_scope.
Definition sym_execTXBI (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXBI_go bc kx t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBI_go_eq : forall t K fuel first stops ss ck,
  sym_execTXBI_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXBI_go sym_execTX_go].
  change (if negb first then existsb (Z.eqb (s_pc ss)) stops else false) with (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool in *; destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBI_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXBI_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXBI (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI, sym_execTX.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXBI_go_eq.
Qed.

End WithSegs.

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition kcutB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0B bc [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0B bc [(wb, wk)] [(kb, kk)] then lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0B bc [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0B bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(hb, ho)])%lzb
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.
Local Close Scope lzb_scope.

Definition kzero_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KZero wb wk wn kb kk len.

Definition kfill_cutB (bc : bctx) (c : Z) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc (fun a n => KFill a n c) wb wk wn kb kk len.

Definition kunk_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KUnk wb wk wn kb kk len.

Definition prune_zfB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  (* [comment removed for export] *)
  if expr_eqb kb wb then
    match len with
    | ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
           else (kcutB bc mk wb k (elen w) kb kk len, [], hints)
    end
  else if apart tt then ([K], [], hints)
  else match kcutB bc mk wb k (elen w) kb kk len with
       | [] => diffbase tt
       | cut => (cut, [], hints)
       end.

Local Open Scope lzb_scope.
Definition prune1pB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pB bc sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) (two64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zfB bc KZero (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zfB bc (fun a n => KFill a n c) (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zfB bc KUnk (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%lzb
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
      else if ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%lzb
      then ([K], [], hints)   (* [comment removed for export] *)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod two64)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%lzb
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition ranges_apart_pcB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%lzb
          | _, _ => false
          end) then true
      else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%lzb then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp tt) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Local Close Scope lzb_scope.

Local Open Scope lzb_scope.
Definition prune1pcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1pB bc sp wa w wv K hints
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%lzb
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.
Local Close Scope lzb_scope.

Fixpoint prunepcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_rangeB bc kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pcB bc sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepcB bc sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.


Lemma kcutB_eqf : forall fk, kcutB (mkbc fk) = (fun mk => kcut mk fk).
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kcut); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkAlu); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SUB); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.split_lit); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf)|] [|@len; @kk; @kb; @wn; @wk; @wb; @mk; @neg; @pos; @x; @hb; @ho; @b; @x5; @x4; @x3; @x2; @x1; @x0; @fk|] "#%*#.#Q#<#5#6#%#$###&#*#'#D#(#I#2#)#E#+#7#9#4#A#H#,#;#=#C#O#-#P#>#1#M#N#K#L#Q#R#S#:#@#G#B#8#J#3#F#?-#I&#J&#:&#K'#L$#M$#N(#(%#O%#P&US0Ok##DOk##S%#k#$D%k#%E#k#&D#k#'D#k#(E#k#)D#'HUS##VS$HGj#*,#'GVS##H'FWS##GHWS$GFH'IXS##FGHXS$FIGH'KYS##IFGHYS$IKFGH'MZS##KIFGHZS$KMIFGH'P[S##MKIFGH[S$MPKIFGHk#+S)Ck#,S)#US*JVS&DE&DEIFUS+$#%$#&DEPM#'#%*%#*$&&DEGQ#+#)#,+#*#(nC#$##C'#%###LnC#$##C)#%#L##+IF(M$NP#(F$NI#$S'%#VJ(#US+O#O$#nC#$##s#:,#%###$&DEKQ#;#9#<8#*3#*$;(QUS1S2VS3S4#&DE%##s###A*#:nC#$##C)#%###LnC#$##C+#%###L$N7KUS,#&DEGH#s#*#s#(&DERJ&DEPQ#s#-#s#+#s#.%#VF'#VF$(nC#$##C$#%###L+GH(J$NR#$N#P+#QnC#$##S%(#%#'##(K$NM#$N#I$S'#(VS('##O#s#(nS&%DE$#-s#_8#$%#.#/#nC#$##s#`;#%###s#*,Os#)#%Rs#>s#<%Rs#=s#?%Rs#9s#>nC#$##C$#%###LnC#$##C&#%#L##nC#$##s#g##%#s#0#s#1%Rs#=s#-%Rs#.s#E%Rs#(s#?nC#$##C$#%###LnC#$##C&#%###L%S-s#$@%S-As#%VS.$#nC#$##S%##%#?#;VS(#7#O#s#<nS&%DE$#-s#ss#,#$%#.#/#nC#$##s#t*#%###s#>,O0#WS/s#v7#j#0s#X#&DEFG#s#X#s#V&DEMK#s#Z#s#X%J%#%J$&&DEHQ#s#^#s#\#s#_*#%J#(nC#$##C'#%###LnC#$##C)#%#L##+FG(G$NF#$S's#/#VP&##O#s#SnC#$##s$.)#%###s#T&DEIQ#s#k#s#i#s#l5#%J0#%J$8%Js#N2nC#$##C$#%###LnC#$##C&#%###LUS,s#:&DEJP&DEMQ#s#u#s#s#s#v%#%S(s#O#%S($s#PVS.$#(P$NJ#$N#M+#QnC#$##S%'#%#s#N##(I$NK#$N#F$S'#(VR'##O#s#onS&%DE$#-s$J5#$%#.#/#nC#$##s$K7#%###s#q,O@#VS5s$M#'JUS6#US7JZS8s$2s$1s#8&$#\S#&PMKIFGH\S$PJMKIFGHWS/s$T$#m#&#j#1D#)Ds$Ws$;s$:#j#2E#)Es$Vs$@s$?#j#3D#)Ds$Ws$Es$D#j#4D#)Ds$Xs$Js$I#j#5E#)Es$Ys$Os$N#j#6D#)Ds$Zs$Ss$V#j#-s$`#)s$as$[s$Ys$W#j#7s$d##"). Qed.
#[export] Hint Rewrite kcutB_eqf : bceq.
Lemma kzero_cutB_eqf : forall fk, kzero_cutB (mkbc fk) = kzero_cut fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kzero_cut); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kcut); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KZero); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB_eqf)|] [|@len; @kk; @kb; @wn; @wk; @wb; @mk; @l; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##\#+#;###$#1#%#&#'#3#5#(#2#)#8#:#/#*#9#.#7#;#<#=#6#4#0%#9$#:(US#Pk#$E#k#%L#k#&E#k#'E#k#(L##CUI#UJC#DVI#CVJDC#FWI#DCWJFDC#GXI#FDCXJGFDC#HYI#GFDCYJHGFDC#KZI#HGFDCZJKHGFDCk##EPk##S$#k#)E7k#*$#VNCQj#*&#[COMKHGFD\NOQMKHGFDWRB$#j#+(#\NOMKHGFDCVS%s#%##MUS&#US'MZS(.,(&$#[I&KHGFDC[JMKHGFDCWRs#,$#m#&#j#,E#$Es#/98#j#-L#$Ls#0>=#j#.E#$Es#1s##B#j#/E#$Es#2s#(s#'#j#0L#$Ls#3s#-s#,#j#1E#$Es#4s#2s#1#j#2s#:##"). Qed.
#[export] Hint Rewrite kzero_cutB_eqf : bceq.
Lemma kfill_cutB_eqf : forall fk, kfill_cutB (mkbc fk) = (fun c => kfill_cut c fk).
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kfill_cut); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kcut); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KFill); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB_eqf)|] [|@len; @kk; @kb; @wn; @wk; @wb; @c; @mk; @n; @a; @l; @x5; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##g#-#=###$#4#%#&#'#3#(#5#7#)#*#9#:#+#1#<#;#0#,#=#>#?#8#6#2%#;$#<(US%Rk#$E#k#%I#k#&E#k#'E#k#(I#k#)E##CUK#VLCDj#*I##DVK#C#FWK#DCWLDFC#GXK#FDCXLFGDC#HYK#GFDCYLGHFDC#JZK#HGFDCZLHJGFDC#M[K#JHGFDC[LJMHGFDCk##ERk##O#k#+#:VPCQj#+%#WS#DCS&j#,E#j#-O#[C#MJHGFD\P$QMJHGFDWS$s#($#j#.+#WS#DCQj#,E#j#-O#\P#NJHGFDCVS's#.##NUS(#US)NZS*42+&$#\K&MJHGFDC\LMNJHGFDCWS$s#5$#m#&#j#/E#$Es#8>=#j#0I#$Is#9s##B#j#1E#$Es#:s#(s#'#j#2E#$Es#;s#-s#,#j#3I#$Is#<s#2s#1#j#4E#$Es#=s#6s#9#j#5I#$Is#>s#<s#:#j#6s#E##"). Qed.
#[export] Hint Rewrite kfill_cutB_eqf : bceq.
Lemma kunk_cutB_eqf : forall fk, kunk_cutB (mkbc fk) = kunk_cut fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kunk_cut); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kcut); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KUnk); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB_eqf)|] [|@len; @kk; @kb; @wn; @wk; @wb; @mk; @l; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##\#+#;###$#1#%#&#'#3#5#(#2#)#8#:#/#*#9#.#7#;#<#=#6#4#0%#9$#:(US#Pk#$E#k#%L#k#&E#k#'E#k#(L##CUI#UJC#DVI#CVJDC#FWI#DCWJFDC#GXI#FDCXJGFDC#HYI#GFDCYJHGFDC#KZI#HGFDCZJKHGFDCk##EPk##S$#k#)E7k#*$#VNCQj#*&#[COMKHGFD\NOQMKHGFDWRB$#j#+(#\NOMKHGFDCVS%s#%##MUS&#US'MZS(.,(&$#[I&KHGFDC[JMKHGFDCWRs#,$#m#&#j#,E#$Es#/98#j#-L#$Ls#0>=#j#.E#$Es#1s##B#j#/E#$Es#2s#(s#'#j#0L#$Ls#3s#-s#,#j#1E#$Es#4s#2s#1#j#2s#:##"). Qed.
#[export] Hint Rewrite kunk_cutB_eqf : bceq.
Lemma prune_zfB_eqf : forall fk, prune_zfB (mkbc fk) = (fun mk => prune_zf mk fk).
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.unit); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune_zfB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune_zf); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kcut); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ktrim); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB_eqf)|] [|@diffbase; @hints; @apart; @len; @kk; @kb; @K; @w; @k; @wb; @mk; @wn; @wk; @l0; @n; @op; @a; @b; @sx; @lo; @e; @k0; @i; @x; @l; @x9; @x8; @x7; @x6; @x5; @x4; @x3; @x2; @x1; @x0; @fk|] "#%1#4#R###&#$#'#(#)#%#,#*#+#;#-#8#?#.#B#D#/#<#0#1#Q#7#=#2#>#A#@#F#H#J#K#G#:#3#R#S#T#E#I#C#9#O#P#N#M#L-#J'#K$#L(#M&#N$#?+#O$#P%#Q%#9$,Ok##MOk##S4#k##S,P,P,S-VS.(#VS.#%k##S,#k#$#$k#%(#k#&*#k#'M#k#(S%#k#)M#k#*O#k#+S*#k#,S%#k#-M#$CUR#VS#CEj#.6#$EVR#C$IWR#ECWS#EIC$DXR#IECXS#IDEC$FYR#DIECYS#DFIEC$GZR#FDIECZS#FGDIEC$H[R#GFDIEC[S#GHFDIEC$K\R#HGFDIEC\S#HKGFDIEC$L]R#KHGFDIEC]S#KLHGFDIEC$J^R#LKHGFDIEC^S#LJKHGFDIEC$N_R#JLKHGFDIEC_S#JNLKHGFDIECk#'Ms#6k#(S%#k#)M#k#/M#k#0S%#k#-M#k#.s#:#VS/CS$j#.s#<#VS0HNZS1S$KHCNJUS2S-#s#Bs#=$##s#=s#?#D)J*N#+#HUS2O&OL##s#Is#D#*#s#Ds#F#D'J[ES$QN#KHG#s#Ms#H#.#s#Hs#J#DnP#$##s#H+#%#'##)Q*S$#+#L&ON.#s#Ts#O#5#s#Os#Q#G'Q[DS'S&S$#JLK#s#Xs#S#9#s#Ss#U#GnP#$##s#S*#%#'##)S$*S&#+#J&OQ9#s#_s#Z#@#s#Zs#\#H'S$[FS+S'S&#NJL#s#cs#^#s#$#s#^s#`#HnP#$##s#^*#%#'##nM#$#'s#_F#+$#1s#%$#29&#3#4#5.&#3#4#5.&#3#4#5.&#3#4#5.'#6#7#2#8#'#6#9#:#2#UDS(&OKs###s#is#d#s#*#s#ds#f#I'L[CQNJ#HGFUES(&OEC#s#os#j#s#0#s#js#l#FnS)$O$#;s#j'#%#&%#9#<#nP#$##s#k-#%#*##nP#$##s#ls#6#%#/##(S$S&QNs#+KHG#s#us#p#s#6#s#ps#r#DnP#$##s#ps#3#%#s#/##(S'S+S&S$s#$JLK#s#ys#t#s#:#s#ts#v#GnP#$##s#ts#+#%#s#(##(S+S5S'S&=NJL#s#}s#x#s#>#s#xs#z#HnP#$##s#xs#$#%#A##nM#$#'s#yF#+$#1s#?$#2+&#3#4#5'&#3#4#5'&#3#4#5'&#3#4#5''#6#7#2#8#'#6#9#:#2#(QS$NJ8HGFnS)$O$#;s#{##%#7%#9#<4nP#$##s#|>#%#;##nP#$##s#}s#G#%#&##WS3s#~4#j#<s#L#VS0GJZS1QHGCJL#s$-s$(#s#J#s$(s$*#I)L*J#+#G#s$2s$-/s#O#s$-s$/#InP#$##s$-%#%#s#(##)N*Q#+#K&OJs#O#s$9s$4#s#V#s$4s$6#F'N(S&S'S$Q#LKH#s$=s$8#s#Z#s$8s$:#FnP#$##s$8*#%#'##nM#$#'s$9D#+$#14$#2.&#3#4#5#&#3#4#5#&#3#4#5#&#3#4#5#'#6#7#2#8s##'#6#9#:#2s##UIS(&OHs#Y#s$Cs$>#s#`#s$>s$@#E'K(NQJL#GFDUCS(#s$Bs$Ds#7DnS)$O$#;s$B%#%#$%#9#<#nP#$##s$C+#%#(##nP#$##s$DB#%#-##VS6s$E#$QUS7#US8QZS9s#rs#ps#(&$#`R&NJLKHGFDIEC`S#NQJLKHGFDIECWS3s$L$#m#&#j#=s$M#%s$Ns$Os$$s$##j#>s$S#%s$Ts$Os$)s$(#j#?s$V#%s$Ws$Ps$.s$-#j#@M#%Ms$Qs$3s$2#j#AS%#%S%s$Rs$8s$7#j#BM#%Ms$Ss$=s$<#j#CO#%Os$Ts$Bs$A#j#DS*#%S*s$Us$Gs$F#j#ES%#%S%s$Vs$Ls$K#j#FM#%Ms$Ws$Ps$S#j#;s$g#%s$hs$Xs$Vs$T#j#Gs$k##"). Qed.
#[export] Hint Rewrite prune_zfB_eqf : bceq.
Lemma prune1pB_eqf : forall fk, prune1pB (mkbc fk) = prune1p fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1p); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.unit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune_zf); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kword_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@Stdlib.Arith.PeanoNat.Nat.eqb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCDisj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KZero); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.app); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KImg); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KFill); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KUnk); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_p); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune_zfB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune_zfB_eqf)|] [|@hints; @K; @wv; @w; @wa; @diffbase; @apart; @len; @kk; @kb; @k; @wb; @mk; @b; @hs; @a; @l0; @n; @op; @sx; @lo; @e; @k0; @i; @z; @p; @x; @lo0; @w'; @v; @bk; @hi; @m; @a1; @n1; @a2; @n2; @c; @k2; @b2; @k1; @b1; @sp; @x4; @x3; @x2; @x1; @x0; @fk|] "#)6#2#o#<#$###%#&#.#)#'#(#/#6#9#-#;#>#D#*#,#+#5#C#0#?#A#\#:#Z#f#8#=#E#M#Q#W#[#_#a#]#k#h#R#B#U#V#1#d#e#m#j#n#o#p#q#N#O#Y#L#I#H#^#@#J#X#K#S#c#b#l#7#G#`#g#i#P#T#F@#X'#Y&#J+#Z'#[$#\%#]$#^%#_$#`%#K+#a%#b$#c$#A/#d$#e%#f$#+*#g(#h%#i%#j%#k%#6$#l$#m%#n&#)*;M;C;QVS0%#VS0#%k#$&#k#%M#k#&P#k#'S,#k#(N#+EUS)#US*E+DVS)#EVS*DE+FWS)#DEWS*FDE+GXS)#FDEXS*GFDE+JYS)#GFDEYS*JGFDE+KZS)#JGFDEZS*KJGFDEk##PMk##N#k##RCk##R=k#)#>k#$B#k#*&#k#+P#k#,S'#k#-P#k#%M#k#'S,#k#.S'#k#/P#k#0/#VS1ES#j#01#)O7D#/G,E#'O($#/S$,%#(#EnC#$##C&#%#S2##<M$MS##<Q#s#<s#:$##s#:s#<#IZS3DEGF-S$#s#?s#=#&#s#=s#?#InC#$##s#=+#%#&##+L0S$0G-%H84$DE#US=S>=S$#=G$nC#$##C$#%###S47S%FnC#$##C$#%###S4.DE)#'$-/HB>.$#-#s#Ps#N97<C#s#Os#Q$#$MS$<0H.GF0K&L%$#$Q#?#s#Ys#W(##s#Ws#Y#E#s#Xs#Z-EnC#$#1s#XD#%#$##nS&$C$#$s#YI#%#-%#1#2#nC#$#*s#Z1#%#s####nC#$##s#[6#%#s#$##nC#$##s#\=#%#s#%##nC#$##s#]s#3#%#B##nN#$#3s#^F#$%#-#,#)S$'S$-s#%Hs#8s#4s#$FDGj##R#.FD)#'$-s#*Hs#=s#9s#)$#G.JG&L:#K$Q#s#4#s#ns#l=##s#ls#n#EnC#$#1s#lD#%###7nS&$C$#$s#mI#%#A%#1#2#nC#$#*s#n*#%#s#7##j##R#_JS-32S%IDEF0K#nN#$#3s#qD#$%#-#,#VS5ES+,D#'H($#/O,%#(#DnC#$##C&#%#S2##$MS%s#G#s$#s#}#s#F#s#}s$##S##s#~s$$s#3S#nC#$##s#~'#%#$##nC#$##s$#)#%#%#$'S(/L,$#(#G$MOs#Q#s$-s$+#s#P#s$+s$-#S$#s$,s$.s#=S$nC#$##s$,'#%#$##'S?/S(,$#(#J$MHs#Z#s$6s$4#s#Y#s$4s$6#O#s$5s$7s#FOnC#$##s$5'#%#$##nP#$#+s$6G#+$#46$#55&#6#3#1,&#6#3#1,&#6#3#1,&#6#3#1,'#7#8#5#9#'#7#:#;#5#-s#WHs#js#fs#Vs#Ls#KG&Ls#Fs#EK$Q#s#`#s$>s$<s#I##s$<s$>#EnC#$#1s$<D#%###s#CnS&$C$#$s$=I#%#s#M%#1#2#nC#$#*s$>)#%#s#c##nC#$##s$?s#q#%#+##nN#$#3s$@F#$%#-#,#)S#'S%VS6#D*F#8F$$M#s#onC#$##s$K%#%###s#p/S#,)#VS7F#*#D8$D$M#s#vnC#$##s$R%#%###s#wWS8M*##s$Ts$R#s#w#s$Rs$T#J3FG*#S++H0S%2S@.#G)#'$2*-)Os#Zs#Y(%$#$MIs$)#s$as$_#s$(#s$_s$a#K0O.,K3JK2#&H&%#$Q#s$/#s$is$gs#I##s$gs$i#EnC#$#1s$gD#%###s#nnS&$C$#$s$hK#%#s#x%#1#2#nC#$#*s$i0#%#-###s$ks$ms#|KnC#$##s$k:#%#$##nS'#$#<s$lE#&#=$#=#$#=#3DF*#S++O)S%0S#.>F)#'$2*-)S$(s#6'%$#$MKs$D#s$|s$z#s$C#s$zs$|#J.s#&J3GJ2#&Os$@%#$Q#s$I#s%'s%%s$K##s%%s%'#EnC#$#1s%%D#%###s$,nS&$C$#$s%&J#%#s$6%#1#2#nC#$#*s%'/#%#,###s%)s%+s$:JnC#$##s%)9#%#$##*-S+)/'0-s$MHs$`s$\s$L$#/.s#6I3KI2#&Ls$?%#$Q#s$Y#s%7s%5s$B##s%5s%7#EnC#$#1s%5D#%###s$<nS&$C$#$s%6I#%#s$F%#1#2#nC#$#*s%7,#%#s$\###s%9s%;s$JInC#$##s%91#%#$##*s#7S++S()H)s#;'s#<-&L%s$)s#>$#s#;0L.s#IS#3IS#2#&S(&%#$Q#s$l#s%Js%Hs#|##s%Hs%J#EnC#$#1s%HD#%###s$OnS&$C$#$s%IS##%#s$Y%#1#2#nC#$#*s%J-#%#s$,##nC#$##s%K3#%###s$,nP#$#>s%Ls#i#+$#<s#>$#5s#%&#6#3#15&#6#3#15&#6#3#15&#6#3#15'#7#?#5#9#'#7#:#;#5#$MJs$v#s%Rs%P#s$u#s%Ps%R#GWSADEJj#5P#j#3N#-:L9s$=s#RFDJj##R#-<L;s$?s#Ts$Os$NJ&S(8s$MI$Q#s$~#s%\s%Zs$2##s%Zs%\#EnC#$#1s%ZD#%###s$anS&$C$#$s%[S##%#s$k%#1#2#nC#$#*s%\)#%#s$>##j##R#_K.s%5s%1S$S#DEG,I#nN#$#3s%_F#$%#-#,#_JS.s$_s$^S%IDEFs$\Ks$OnN#$#3s%aD#$%#-#,#nM#$#%s%bF#-&#3#@#As$b%#3#+s$O&#3#+#Bs$$%#8#C8%#9#D5&#9#8#Cs#G%#3#55'#E#F#G#Hs#b&#3#+#I%%#3#+#9s%5s%2nC#$##s%d##%#s%-#s%*%LHs%<s%8s%(DEs%':s%%s%$:#s%#%LHs%?s%;s%+s$}s$|s%*nC#$#*s%i##%#s%2#s$nnC#$##s%j%#%#s%3##nC#$##s%k(#%#s%4##nC#$##s%ls%B#%#*##nN#$#3s%mF#$%#-#,#%LHs%Es%As%1FDGj##R#%LHs%Gs%Cs%3s$js$iGnC#$#*s%q##%#s%:#s$bj##R#1S-Hs$rs$qS%IDEF&K#nN#$#3s%tD#$%#-#,#4SBUS9#4$4#4#4#4#US9#VSC)#VS5E#,D#(#s$j9#s$gnC#$##s&&##%#s$d#s$cnP#$#+s&'G#+$#4#$#5s$b&#6#3#1s$Y&#6#3#1s$Y&#6#3#1s$Y&#6#3#1s$Y'#7#8#5#9s$P'#7#:#;#5s$P%LHs%[s%Ws%Gs%=s%<GnC#$#*s&)##%#s%N#s$JnC#$##s&*s%\#%#%##nN#$#3s&+F#$%#-#,#*s$8-%HOs%,s%+s$6s$3s$2s$1nC#$#*s&.##%#s$.#s$$nC#$##s&/%#%###s$#nS'#$#<s&0E#&#s$=$#=#$#=#*s#~2%OS$s#|s$Ns#{s#ys#xs#wnC#$#*s&3##%#s#t#s#knC#$##s&4%#%###s#j*s#t6%LHs%is%es%Us#is#hs#tnC#$#*s&7##%#s%\#s#_nC#$##s&8%#%###s#^*s$6:%S(Ls#\s%$s$9s#[s#Zs$6nC#$#*s&;##%#s$y#s#PnC#$##s&<%#%###s$ynP#$#>s&=s$Z#+$#</$#5+&#6#3#1'&#6#3#1'&#6#3#1'&#6#3#1''#7#?#5#9#'#7#:#;#5#%S(Ls#`s%(s$=FDJj##R#%S(Ls#bs%*s$?s%:s%9JnC#$#*s&A##%#s%##s#Dj##R#1s#OLs%vs%rS$S#DEG&I#nN#$#3s&DF#$%#-#,#1S.Hs%Ds%CS%IDEFs#4Ks#1nN#$#3s&FD#$%#-#,#nM#$#%s&GF#-&#3#@#As#8%#3#+s#1&#3#+#B>%#8#C,%#9#Ds#V&#9#8#Cs$,%#3#5s#V'#E#F#G#Hs$G&#3#+#I%%#3#+#>s&Hs#D#j#=s&##k#HPCk#JS'#k#KP#k#FP#k#LS'#k#MP#k#NS/#US:I5Hs&)s&%s%qDEs%p5Hs&*s&&s%rs%hs%gs%qnC#$#*s&T##%#s%y#s%YnC#$##s&Us%l#%#s%z##nC#$##s&V&#%#s%{##nC#$##s&Ws&-#%#s%x##nN#$#3s&XF#$%#-#,#5Hs&0s&,s%xFDGj##R#5Hs&2s&.s%zs%Us%TGnC#$#*s&\##%#s&%#s%Mj##R#1S-Hs%]s%\S%IDEF&K#nN#$#3s&_D#$%#-#,#5Hs&7s&3s&#s%us%tGnC#$#*s&a##%#s&*#s%&nC#$##s&bs&8#%#s%.##nN#$#3s&cF#$%#-#,#[JOs%cs%bs$ms$js$is$hnC#$#*s&e##%#s$e#s$[nC#$##s&fs$q#%###s$ZnS'#$#<s&gE#&#s$t$#=#$#=#[GS$s$Vs%(s$Us$Ss$Rs$QnC#$#*s&i##%#s$N#s$EnC#$##s&js$Z#%###s$D5Hs&Bs&>s&.s$Bs$As$MnC#$#*s&l##%#s&5#s$8nC#$##s&ms$E#%###s$7?Ls$4s%Xs$ms$3s$2s$jnC#$#*s&o##%#s%Q#s$(nC#$##s&ps$8#%###s%QnP#$#>s&qs%2#+$#<,$#5)&#6#3#1&&#6#3#1&&#6#3#1&&#6#3#1&'#7#?#5#9#'#7#:#;#5#?Ls$8s%\s$qFDJj##R#?Ls$:s%^s$ss%ns%mJnC#$#*s&u##%#s%W#s#xj##R#1s$'Ls&Ns&JS$S#DEG&I#nN#$#3s&xF#$%#-#,#1S.Hs%xs%wS%IDEFAK>nN#$#3s&zD#$%#-#,#nM#$#%s&{F#-&#3#@#As#%%#3#+>&#3#+#B:%#8#C,%#9#Ds$.&#9#8#Cs$`%#3#5s$.'#E#F#G#Hs${&#3#+#I%%#3#+#>s&|#s#7j#1s#/#7Ds%}(s&Ss%}/S%,s&##(#E9&#ZS3DEGFs&&S%#s'-s'+#s&P#s'+s'-#KnC#$##s'+&#%#s%+##%HOs&+s&*s%5DEs&J=S%s&I:#s&H7S#F:$#%HOs&0s&/s%:s&Fs&Es&O&Hs%1s&?s&>$Q#s&Z#s'8s'6s%t##s'6s'8#EnC#$#1s'6D#%###s&=nS&$C$#$s'7K#%#s&G%#1#2#nC#$#*s'8)#%#s%8##nC#$##s'9+#%#s%9##nC#$##s':0#%#s%:##nC#$##s';;#%#2##nN#$#3s'<F#$%#-#,#%HOs&<s&;s%FFDGj##R#%HOs&>s&=s%Hs&9s&8G&Hs%?s&7K$Q#s&h#s'Fs'Ds&&##s'Ds'F#EnC#$#1s'DD#%###s&KnS&$C$#$s'EK#%#s&U%#1#2#nC#$#*s'F)#%#s%F##j##R#1S-Os%6s%dS#KDEF,J#nN#$#3s'ID#$%#-#,#(s$)s&y(s&wD9$#nC#$##s'M##%#s&r#s$snC#$##s'N%#%#s&s#s$t'L/H,$#(#G#s'Ws'Us&bs&z#s'Us'W#S%#s'Vs'Xs&gS%nC#$##s'V&#%#$##(s&3JnC#$##s'X##%#s&0#s&/nP#$#+s'YG#+$#4.$#5-&#6#3#1%&#6#3#1%&#6#3#1%&#6#3#1%'#7#8#5#9#'#7#:#;#5#%HOs&Ys&Xs%cs&os&nG&Hs%Zs&hK$Q#s''#s'as'_s&A##s'_s'a#EnC#$#1s'_D#%###s&fnS&$C$#$s'`K#%#s&p%#1#2#nC#$#*s'a)#%#s%a##nC#$##s'bs#B#%#+##nN#$#3s'cF#$%#-#,#)I'S#VS6#D*F#8F$$M#s'6nC#$##s'n%#%###s'7/I,)#VS7F#*#D8$D$M#s'=nC#$##s'u%#%###s'>WS8M*##s'ws'u#s'>#s'us'w#G%OS$s%cs&5s%bs%{s%zs%y&Os'9s%ts%r$Q#s'B#s'|s'zs'D##s'zs'|#EnC#$#1s'zD#%###s'%nS&$C$#$s'{J#%#s'/%#1#2#nC#$#*s'|)#%#s%a##nC#$##s'}s$S#%###s%WnS'#$#<s'~E#&#,$#=#$#=#0I%S$S%s&A=#s%ks%js%i&S$s&.s%es%c$Q#s'M#s(+s()s&)##s()s(+#EnC#$#1s()D#%###s'0nS&$C$#$s(*G#%#s':%#1#2#nC#$#*s(+)#%#s%:###s(-s(/s'>GnC#$##s(-s$Z#%#$##%HOs'-s',s&7s%as%`s%l&Hs&.s%_s%]$Q#s'W#s(5s(3s&q##s(3s(5#EnC#$#1s(3D#%###s':nS&$C$#$s(4K#%#s'D%#1#2#nC#$#*s(5)#%#s&5##nC#$##s(6s$_#%###s&*%LHs'js'fs'Vs%Xs%Ws&3&Ls'Fs%Us%S$Q#s'`#s(>s(<s'I##s(<s(>#EnC#$#1s(<D#%###s'CnS&$C$#$s(=I#%#s'M%#1#2#nC#$#*s(>)#%#s'c##nC#$##s(?s$d#%###s%enP#$#>s(@s#:#+$#<@$#55&#6#3#1,&#6#3#1,&#6#3#1,&#6#3#1,'#7#?#5#9#'#7#:#;#5#$MGs'j#s(Fs(D#s'i#s(Ds(F#F%LHs'ws'ss'cFDJj##R#%LHs'ys'us'es'@s'?J&Ls'Us'>I$Q#s'o#s(Ms(Ks'X##s(Ks(M#EnC#$#1s(KD#%###s'RnS&$C$#$s(LI#%#s'\%#1#2#nC#$#*s(M)#%#s'r##j##R#1s%[Hs'Ns'MS%IDEG,K#nN#$#3s(PF#$%#-#,#1S.Os&?s&mS#KDEFs#qJs#hnN#$#3s(RD#$%#-#,#nM#$#%s(SD#-&#3#@#As#u%#3#+s#h&#3#+#Bs#N%#8#C5%#9#D2&#9#8#Cs%b%#3#52'#E#F#G#Hs&8&#3#+#I%%#3#+#VSDs(T#+IUS;#USEIZS<s$fs$es$9&$#USF&USGIZS<s(5s(3s$p%$#[S))KJGFDE[S*IKJGFDE>s(^$#m#&#j#Os(c#6s(ds(as(Ks(J#j#PM#6Ms(bs(Ps(O#j#QP#6Ps(cs(Us(T#j#RS,#6S,s(ds(Zs(Y#j#SN#6Ns(es(_s(^#j#>S/#6S/s(fs(ds(c#j#Ts(p##"). Qed.
#[export] Hint Rewrite prune1pB_eqf : bceq.
Lemma ranges_apart_pcB_eqf : forall fk, ranges_apart_pcB (mkbc fk) = ranges_apart_pc fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_pc); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.in_sides_x); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_rng); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sidesB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_D); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apartB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_h1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.end_hiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sp_Dx); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.shares_var); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.in_sides); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_apart); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.end_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_apartB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.end_hiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sidesB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sides_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.in_sides_xB_eqf)|] [|@n2; @k2; @b2; @br2; @n1; @k1; @b1; @D; @p0; @lo2; @hi2; @p; @lo1; @hi1; @x; @e1; @e2; @h2; @h1; @z2; @n; @op; @a; @b; @sx; @lo; @e; @k; @i; @z1; @o; @neg; @pos; @x6; @x5; @x4; @x3; @x2; @x1; @x0; @fk|] "#+\#:#n#E#B#R#C#Q###D#(#A#%#&#$#)#'#+#-#.#/#,#0#1#*#2#3#5#4#6#a#F#H#7#Z#8#9#c#d#=#K#T#S#U#f#h#g#e#W#]#X#@#>#J#`#i#j#k#l#m#n#o#p#O#^#N#G#_#b#?#L#M#V#Y#\#[#I#P:#_%#`&#a%#b$#c'#L*#N&#R*#Q&#d%#e(#f&#g$#h$#i%#j%#k$#O%#H(#l)#P%#m$#)%US7SD9DDUF#k#$KCk#%D#k#&K#k#'&#k#(K#k#)D#k#*K#&HUS/#US0H&NVS/#HVS0NH&LWS/#NHWS0LNH&MXS/#LNHXS0MLNH&PYS/#MLNHYS0PMLNH&JZS/#PMLNHZS0JPMLNH&O[S/#JPMLNH[S0OJPMLNH&S(\S/#OJPMLNH\S0S(OJPMLNH9SEKUS7#k#+#AUS8Q/R#MS'8S(#$##NR%$##HR8O#$##PS'%$#nC#$##C(#%#G##nI%DD$#,CH#$%#-#.#nF$s#4$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s#6$#2C1#%$#/##E&S#US9R8HYS:%$JP#8N[S;'S%Q#JP%nC#$##C%#%#G##nC#$##C*#%#G##0S*&S+7#R#JS*##N#MS$%$##LS$##H#OS*%$#nC#$##C'#%#G##&S-*#S,S*S)OJN#PS&%H#nF$D$#2C%#%$#3##E*'S&S$S#MLH#S(S,%H#nF$D$#2C%#%$#4##EnC#$##C'#%#G##nC#$##C-#%#G##nF$D$#2C7#%$#5##EnF$D$#2C:#%$#6##EnI%DD$#,CH#$%#-#.#nF$s#Y$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s#[$#2Cs#6#%$#/##E1RS2XL#JPM2S%J3#9KD'KDJPUSF$$%$#'KDS%Q'KDS(S.$(#&$)%#+s#3'#$+')'KDMS.$-#+$.-#+s#8&#nC#$##C(#%#G##nC#$##C2#%#E##nC#$##C5#%#G##nC#$##C8#%#G##/S$0S+&S17#S$#JS+##N%#s#R#LS'##H#OS+%$#nC#$##C'#%#G##&S3*#S-S+S,OJN#PS)%H#nF$D$#2C%#%$#3##E*'S)S'S&MLH#S(S-%H#nF$D$#2C%#%$#4##EnC#$##C'#%#G##nC#$##C-#%#G##nF$D$#2C6#%$#5##EnF$D$#2C9#%$#6##EnI%DD$#,CH#$%#-#.#nF$s$0$#'CS##%$#,##EnI%DD$#/CH#$%#0#1#nF$s$2$#2C>#%$#/##E1S$S2XP#S(OJ2S#S(3#&S&'KDS(O$s#7#s#5'KDS#R'KDS%S.$s#:#s#8$s#;%#+)'#$s#='s#;'KDJS.$s#?#s#=$s#@,#+.&#nC#$##C(#%#G##nC#$##C1#%#E##nC#$##C4#%#G##nC#$##C7#%#G##/S&0S-7s#*S&#JS-##N#MS)%$##LS)##H#OS-%$#nC#$##C'#%#G##&S4*#S1S-S+OJN#PS*%H#nF$D$#2C%#%$#3##E*'S*S)S'MLH#S(S1%H#nF$D$#2C%#%$#4##EnC#$##C'#%#G##nC#$##C-#%#G##nF$D$#2C7#%$#5##EnF$D$#2C9#%$#6##EnI%DD$#,CH#$%#-#.#nF$s$b$#'CS$#%$#,##EnI%DD$#/CH#$%#0#1#nF$s$d$#2C>#%$#/##E1S&S2XJ#QS(O2S$Q3#&S''KDQS($s#i#s#g'KDS$S#'KDRS.$s#l#s#j$s#m%#+)'#$s#o's#m'KDOS.$s#q#s#o$s#r,#+.&#nC#$##C(#%#G##nC#$##C1#%#E##nC#$##C4#%#G##nC#$##C7#%#G##nK#$#$CL#+$#7s$>$#8s#g&#9#:#;s#5&#9#:#;s#5&#9#:#;s#5&#9#:#;s#5'#<#=#8#>#'#<#?#@#8#/S%0S)&S,7#S%#JS)##N#MS#%$##LS###H#OS)%$#nC#$##C'#%#G##*s$JS*S)S'OJN#PS$%H#nF$D$#2C%#%$#3##E*s$NS$S#RMLH#S(S*%H#nF$D$#2C%#%$#4##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#2C6#%$#5##EnF$D$#2C9#%$#6##EnI%DD$#,CH#$%#-#.#nF$s%9$#'CQ#%$#,##EnI%DD$#/CH#$%#0#1#nF$s%;$#2C>#%$#/##E1S%S2XN#PML2QP3#&R'KDPM$s$@#s$>+%#s#-'KDLS.$s$C#s$A$s$D'#+)s#:#nC#$##C'#%#G##nC#$##C,#%#E##nC#$##C/#%#G##nC#$##C2#%#G##/S#0S,7s$aS##JS,##N#MS&%$##LS&##H#OS,%$#nC#$##C'#%#G##*s$BS+S,S*OJN%Hs%+nF$D$#2C$#%$#3##E*s$ES'S&S$MLH#S(S+%H#nF$D$#2C%#%$#4##EnC#$##C'#%#G##nC#$##C+#%#G##nF$D$#2C5#%$#5##EnF$D$#2C7#%$#6##EnI%DD$#,CH#$%#-#.#nF$s%d$#'CR#%$#,##EnI%DD$#/CH#$%#0#1#nF$s%f$#2C<#%$#/##E1S#S2XM#OJP2RO3#&S$'KDOJ$s$k#s$i'KDRS%'KDQS.$s$n#s$l$s$o%#+)'#$s$q's$o'KDPS.$s$s#s$q$s$t,#+.&#nC#$##C(#%#G##nC#$##C1#%#E##nC#$##C4#%#G##nC#$##C7#%#G##nK#$#(CJ#+$#As#`$#8s#3&#9#:#;#&#9#:#;#&#9#:#;#&#9#:#;#'#<#=#8#>s$7'#<#?#@#8s$7,s%Ss%NnI%DD$#,CH#$%#-#.#nF$s&#$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s&%$#2Cs%\#%$#/##EYS5S#s%LJPs%K[S6S#S%Qs%JJPs%LnC#$##C$#%#G##nC#$##C&#%#G##4S+R,s%Ds%@(S-S,S*S)OJNnF$D$#2C##%$#3s%=#E(S-S&S$S#MLHnF$D$#2C##%$#4s%;#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#2C*#%$#5##EnF$D$#2Cs%R#%$#6##EnI%DD$#,CH#$%#-#.#nF$s&5$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s&7$#2Cs%n#%$#/##E5S#s%:JPM)S#s%4s%0)S#s%/s%,nC#$##C$#%#G##nC#$##Cs%;#%#E##nC#$##C'#%#G##nC#$##C)#%#G##4S1S$,s%&s$~(S3S-S+S,OJNnF$D$#2C##%$#3s${#E(S3S)S'S&MLHnF$D$#2C##%$#4s$y#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#2C*#%$#5##EnF$D$#2Cs%3#%$#6##EnI%DD$#,CH#$%#-#.#nF$s&J$#'CS##%$#,##EnI%DD$#/CH#$%#0#1#nF$s&L$#2Cs%8#%$#/##E5S&s$xS(OJ)S&s$ss$o)S&s$ns$knC#$##C$#%#G##nC#$##Cs$y#%#E##nC#$##C'#%#G##nC#$##C)#%#G##4S3S&,s$es$a(S4S1S-S+OJNnF$D$#2C##%$#3s$^#E(S4S*S)S'MLHnF$D$#2C##%$#4s$\#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#2C*#%$#5##EnF$D$#2Cs$r#%$#6##EnI%DD$#,CH#$%#-#.#nF$s&_$#'CS$#%$#,##EnI%DD$#/CH#$%#0#1#nF$s&a$#2Cs$w#%$#/##E5S's$[QS(O)S's$Vs$R)S's$Qs$NnC#$##C$#%#G##nC#$##Cs$\#%#E##nC#$##C'#%#G##nC#$##C)#%#G##nK#$#$CL#+$#7s#B$#8s#-&#9#:#;8&#9#:#;8&#9#:#;8&#9#:#;8'#<#=#8#>#'#<#?#@#8#4S,S%,s$Gs$C(S+S*S)S'OJNnF$D$#2C##%$#3s$A#E(S+S$S#RMLHnF$D$#2C##%$#4s$?#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#2C*#%$#5##EnF$D$#2Cs$U#%$#6##EnI%DD$#,CH#$%#-#.#nF$s&u$#'CQ#%$#,##EnI%DD$#/CH#$%#0#1#nF$s&w$#2Cs$Z#%$#/##E5Rs$>PML)Rs$9s$c)Rs$ms$6nC#$##C$#%#G##nC#$##Cs$?#%#E##nC#$##C'#%#G##nC#$##C)#%#G##4S-S#,s$0s$,(S1S+S,S*OJNnF$D$#2C##%$#3s$+#E(S1S'S&S$MLHnF$D$#2C##%$#4s$)#EnC#$##C%#%#G##nC#$##C(#%#G##nF$D$#2C*#%$#5##EnF$D$#2Cs$=#%$#6##EnI%DD$#,CH#$%#-#.#nF$s'.$#'CR#%$#,##EnI%DD$#/CH#$%#0#1#nF$s'0$#2Cs$B#%$#/##E5S$s$(OJP)S$s$#s#{)S$s#zs#wnC#$##C$#%#G##nC#$##Cs$)#%#E##nC#$##C'#%#G##nC#$##C)#%#G##nK#$#(CJ#+$#As#-$#88&#9#:#;#&#9#:#;#&#9#:#;#&#9#:#;#'#<#=#8#>s#C'#<#?#@#8s#C.Cs#w#j#;s&s#k#$DCk#%D#k#&K#k#+s&x#US5QXLs&fJPs&enC#$##C##%#G#s&cnC#$##Cs&j#%#G##nC#$##Cs#i#%#G#s&2nC#$##Cs&G#%#G##nC#$##Cs#V#%#G#s%^nC#$##Cs%r#%#G##nC#$##Cs#C#%#G#s%.nC#$##Cs%B#%#G##nK#$#$CL#+$#7)$#8'&#9#:#;%&#9#:#;%&#9#:#;%&#9#:#;%'#<#=#8#>#'#<#?#@#8#nC#$##Cs#0#%#G#s$_nC#$##Cs$n#%#G##nC#$##C=#%#G#s$1nC#$##Cs$E#%#G##nK#$#(CJ#+$#A'$#8%&#9#:#;#&#9#:#;#&#9#:#;#&#9#:#;#'#<#=#8#>*'#<#?#@#8*.C#9j#;4#UFDk#6D#k#1D#k#0D#k#8K#k#?D#k#;K#US<QnC#$##Cs$5#%#G#s&{nC#$##Cs'&#%#G##ZRS,S*S)OJNnF$D$#2C##%$#3s&l#EZRS&S$S#MLHnF$D$#2C##%$#4s&j#EnC#$##C%#%#G##nC#$##Cs&t#%#G##nF$D$#2Cs&~#%$#5##EnF$D$#2Cs'%#%$#6##EnI%DD$#,CH#$%#-#.#nF$s'd$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s'f$#2Cs'A#%$#/##EnC#$##C##%#G#s#&ZS$S-S+S,OJNnF$D$#2C##%$#3s&F#EZS$S)S'S&MLHnF$D$#2C##%$#4s&D#EnC#$##C%#%#G##nC#$##Cs&N#%#G##nF$D$#2Cs&W#%$#5##EnF$D$#2Cs&Z#%$#6##EnI%DD$#,CH#$%#-#.#nF$s'q$#'CS##%$#,##EnI%DD$#/CH#$%#0#1#nF$s's$#2Cs&_#%$#/##EnC#$##C##%#G#s#1ZS&S1S-S+OJNnF$D$#2C##%$#3s%}#EZS&S*S)S'MLHnF$D$#2C##%$#4s%{#EnC#$##C%#%#G##nC#$##Cs&)#%#G##nF$D$#2Cs&3#%$#5##EnF$D$#2Cs&5#%$#6##EnI%DD$#,CH#$%#-#.#nF$s'~$#'CS$#%$#,##EnI%DD$#/CH#$%#0#1#nF$s($$#2Cs&:#%$#/##EnC#$##C##%#G#s#<nK#$#$CL#+$#7s#*$#8=&#9#:#;0&#9#:#;0&#9#:#;0&#9#:#;0'#<#=#8#>#'#<#?#@#8#ZS%S*S)S'OJNnF$D$#2C##%$#3s%X#EZS%S$S#RMLHnF$D$#2C##%$#4s%V#EnC#$##C%#%#G##nC#$##Cs%_#%#G##nF$D$#2Cs%i#%$#5##EnF$D$#2Cs%l#%$#6##EnI%DD$#,CH#$%#-#.#nF$s(0$#'CQ#%$#,##EnI%DD$#/CH#$%#0#1#nF$s(2$#2Cs%q#%$#/##EnC#$##C##%#G#s#GZS#S+S,S*OJNnF$D$#2C##%$#3s%:#EZS#S'S&S$MLHnF$D$#2C##%$#4s%8#EnC#$##C%#%#G##nC#$##Cs%@#%#G##nF$D$#2Cs%J#%$#5##EnF$D$#2Cs%L#%$#6##EnI%DD$#,CH#$%#-#.#nF$s(=$#'CR#%$#,##EnI%DD$#/CH#$%#0#1#nF$s(?$#2Cs%Q#%$#/##EnC#$##C##%#G#s#RnK#$#(CJ#+$#A=$#80&#9#:#;#&#9#:#;#&#9#:#;#&#9#:#;#'#<#=#8#>s#+'#<#?#@#8s#+.C#s#hj#Bs#J#k#CS=Ck#DS=#US>QnC#$##Cs'[#%#G#s$unF$D$#2Cs'e#%$#5##EnF$D$#2Cs'h#%$#6##EnI%DD$#,CH#$%#-#.#nF$s(K$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s(M$#2Cs((#%$#/##EVLs'Is'EVLs'Ds'AnC#$##C$#%#G##nC#$##Cs'P#%#E##nC#$##Cs$x#%#G##nC#$##C(#%#G##nC#$##Cs'5#%#G#s$mnF$D$#2Cs'>#%$#5##EnF$D$#2Cs'A#%$#6##EnI%DD$#,CH#$%#-#.#nF$s(X$#'CS##%$#,##EnI%DD$#/CH#$%#0#1#nF$s(Z$#2Cs'F#%$#/##EVPs'$s&|VPs&{s&xnC#$##C$#%#G##nC#$##Cs'*#%#E##nC#$##Cs$p#%#G##nC#$##C(#%#G##nC#$##Cs&l#%#G#s$enF$D$#2Cs&v#%$#5##EnF$D$#2Cs&x#%$#6##EnI%DD$#,CH#$%#-#.#nF$s(e$#'CS$#%$#,##EnI%DD$#/CH#$%#0#1#nF$s(g$#2Cs&}#%$#/##EVJs&[s&WVJs&Vs&SnC#$##C$#%#G##nC#$##Cs&a#%#E##nC#$##Cs$h#%#G##nC#$##C(#%#G##nK#$#$CL#+$#7s#r$#8=&#9#:#;0&#9#:#;0&#9#:#;0&#9#:#;0'#<#=#8#>#'#<#?#@#8#nC#$##Cs&F#%#G#s$]nF$D$#2Cs&P#%$#5##EnF$D$#2Cs&S#%$#6##EnI%DD$#,CH#$%#-#.#nF$s(s$#'CQ#%$#,##EnI%DD$#/CH#$%#0#1#nF$s(u$#2Cs&X#%$#/##EVNs&6s&`VNs&js&3nC#$##C$#%#G##nC#$##Cs&<#%#E##nC#$##Cs$`#%#G##nC#$##C(#%#G##nC#$##Cs&'#%#G#s$UnF$D$#2Cs&1#%$#5##EnF$D$#2Cs&3#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)$$#'CR#%$#,##EnI%DD$#/CH#$%#0#1#nF$s)&$#2Cs&8#%$#/##EVMs%ts%pVMs%os%lnC#$##C$#%#G##nC#$##Cs%z#%#E##nC#$##Cs$X#%#G##nC#$##C(#%#G##nK#$#(CJ#+$#A=$#80&#9#:#;#&#9#:#;#&#9#:#;#&#9#:#;#'#<#=#8#>s#+'#<#?#@#8s#+.C#s$Tj#;s#H#k#>Ks$=US?QUS%RnF$D$#2C##%$#5s#J#EnF$D$#2Cs(S#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)6$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s)8$#2Cs(o#%$#/##EnC#$##C##%#G#s%ZUS#S$nF$D$#2C##%$#5s#E#EnF$D$#2Cs('#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)>$#'CS##%$#,##EnI%DD$#/CH#$%#0#1#nF$s)@$#2Cs(,#%$#/##EnC#$##C##%#G#s%MUS$S&nF$D$#2C##%$#5s#@#EnF$D$#2Cs'Y#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)F$#'CS$#%$#,##EnI%DD$#/CH#$%#0#1#nF$s)H$#2Cs'^#%$#/##EnC#$##C##%#G#s%@nK#$#$CL#+$#7s$N$#83&#9#:#;+&#9#:#;+&#9#:#;+&#9#:#;+'#<#=#8#>#'#<#?#@#8#UQS%nF$D$#2C##%$#5s#;#EnF$D$#2Cs'/#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)O$#'CQ#%$#,##EnI%DD$#/CH#$%#0#1#nF$s)Q$#2Cs'4#%$#/##EnC#$##C##%#G#s%3URS#nF$D$#2C##%$#5s#6#EnF$D$#2Cs&f#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)W$#'CR#%$#,##EnI%DD$#/CH#$%#0#1#nF$s)Y$#2Cs&k#%$#/##EnC#$##C##%#G#s%&nK#$#(CJ#+$#A3$#8+&#9#:#;#&#9#:#;#&#9#:#;#&#9#:#;#'#<#=#8#><'#<#?#@#8<.C#s%&j#Bs#/#k#(Ds%#k#)D#k#*K#US6QZLS%Qs))JPs)+nC#$##Cs&?#%#G##nC#$##Cs)0#%#G##nF$D$#2Cs&=#%$#5s#|#EnF$D$#2Cs))#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)h$#'CS%#%$#,##EnI%DD$#/CH#$%#0#1#nF$s)j$#2Cs)E#%$#/##EnC#$##C##%#G#s&0nF$D$#2Cs&/#%$#5s#v#EnF$D$#2Cs(X#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)o$#'CS##%$#,##EnI%DD$#/CH#$%#0#1#nF$s)q$#2Cs(]#%$#/##EnC#$##C##%#G#s%~nF$D$#2Cs%}#%$#5s#p#EnF$D$#2Cs(-#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)v$#'CS$#%$#,##EnI%DD$#/CH#$%#0#1#nF$s)x$#2Cs(2#%$#/##EnC#$##C##%#G#s%pnK#$#$CL#+$#78$#81&#9#:#;*&#9#:#;*&#9#:#;*&#9#:#;*'#<#=#8#>#'#<#?#@#8#nF$D$#2Cs%o#%$#5s#j#EnF$D$#2Cs'^#%$#6##EnI%DD$#,CH#$%#-#.#nF$s)~$#'CQ#%$#,##EnI%DD$#/CH#$%#0#1#nF$s*$$#2Cs'c#%$#/##EnC#$##C##%#G#s%bnF$D$#2Cs%a#%$#5s#d#EnF$D$#2Cs'8#%$#6##EnI%DD$#,CH#$%#-#.#nF$s*)$#'CR#%$#,##EnI%DD$#/CH#$%#0#1#nF$s*+$#2Cs'=#%$#/##EnC#$##C##%#G#s%TnK#$#(CJ#+$#A1$#8*&#9#:#;#&#9#:#;#&#9#:#;#&#9#:#;#'#<#=#8#>9'#<#?#@#89.C#s%Tj#;s#-##s'=s)e#NS%%$##HS%##s)d%#s)F,&#nI%DD$#,CH#$%#-#.#nF$s*8$#'CQ#%$#,##EnI%DD$#/CH#$%#0#1#nF$s*:$#2Cs'y#%$#/##EUS9S%YS5R#PMs)a[S6RQS(s)`PMs)bnC#$##C$#%#G##nC#$##C'#%#G##nK#$#$CN#+$#7#$#8s%|&#9#:#;s%g&#9#:#;s%g&#9#:#;s%g&#9#:#;s%g'#<#=#8#>s&K'#<#?#@#8s&K/Q0S'4S*Q#JS'##N#MR%$##LR##H#OS'%$#,'#(S,S)S'S&OJN#PS#%H#nF$D$#2C%#%$#3##E(S,S#RS%MLH#S(S)%H#nF$D$#2C%#%$#4##EnC#$##C'#%#G##nC#$##C,#%#G##nF$D$#2C6#%$#5##EnF$D$#2C8#%$#6##EnI%DD$#,CH#$%#-#.#nF$s*Z$#'CS(#%$#,##EnI%DD$#/CH#$%#0#1#nF$s*\$#2C=#%$#/##E1QS25S%#MLN2S(M3#'KDML$s)`#s)^)S%#s)#'KDNS.$s)c#s)a$s)d'#)S%s)0#nC#$##C'#%#G##nC#$##C+#%#E##nC#$##C.#%#G##nC#$##C1#%#G##nK#$#(CP#+$#As#.$#8#&#9#:#;s'0&#9#:#;s'0&#9#:#;s'0&#9#:#;s'0'#<#=#8#>s&7'#<#?#@#8s&7VSGC#&QUS;#USHQ6s#os#ns#D&$#US@&USIQ6s$Fs$Es#u%$#USA)USJQ6s%4s%3s$J%$#USB,USKQ6s&%s&$s%9%$#US:/USLQ6s&As&@s&/%$#USM2USNQ6s*]s*\s&H%$#]S/5S(OJPMLNH]S0QS(OJPMLNH.C$#m#&#j#EK#-KCs*gs*f#j#FD#-Ds+*s*ls*k#j#GK#-Ks++s*qs*p#j#Hs+.#-s+/s+,s*vs*u#j#IK#-Ks+-s*{s*z#j#JD#-Ds+.s+$s+##j#KK#-Ks+/s+)s+(#j#2SC#-SCs+0s+.s+-#j#Ls+:##"). Qed.
#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Lemma prune1pcB_eqf : forall fk, prune1pcB (mkbc fk) = prune1pc fk.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1pc); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_pc); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.Arith.PeanoNat.Nat.eqb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SCDisj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1p); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kzero_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kfill_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kunk_cut); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pcB_eqf)|] [|@br2; @hints; @K; @wv; @w; @wa; @n2; @k2; @b2; @n1; @k1; @b1; @sp; @b; @hs; @apart; @a; @kb; @kk; @x; @k0; @l; @w'; @v; @len; @bk; @lo; @hi; @e; @m; @n; @a1; @a2; @c; @p; @wn; @wk; @wb; @x5; @x4; @x3; @x2; @x1; @x0; @fk|] "#&h#1#`#;#$#%###5#&#8#(#*#)#/#.#4#'#,#-#+#:#0#>#?#@#B#9#7#Y#Z#[#D#Q#R#T#U#V#W#H#<#O#P#\#]#^#_#`#a#b#K#A#L#J#6#S#E#F#C#G#I#X#=#M#N7#Q'#R$#S&#?,#T$#U(#V'#W&#X%#E*#Y)#Z$#F*#[$#*+#\%#/$#]%#^$#_%3G3C4S&S&US7#3S'4'#4#'k#$&#k#%)#k#&G#k#'S$#k#(S*#k#)I#$FUS(#US)F$DVS(#FVS)DF$EWS(#DFWS)EDF$HXS(#EDFXS)HEDF$PYS(#HEDFYS)PHEDF$JZS(#PHEDFZS)JPHEDF$L[S(#JPHEDF[S)LJPHEDFk#*S$Ck#+S&#k#,S$#k#$s#$#k#-S$#k#.S&#k#/S$#k#0S+#US/K.N+D#$S%/#MNRQS#K0N'R'H1M)%$LDF#5G%GS##5S'#s#8s#4$##s#4s#8#KUS8S96R#6H$nC#$##C$#%###S0+QEnC#$##C$#%###S0VS1DF.#0$1M843L$#2#s#Ds#@1/5C#s#As#E$#%GR4'MVS1HE'J)S%%$#%S'#7#s#Ms#I(##s#Is#M#F#s#Js#N-FnC#$#1s#JD#%#$##nO$C$#%s#KK#%#-%#1#2#nC#$#3s#L1#%#;##nC#$##s#M6#%#<##nC#$##s#NB#%#=##nC#$##s#Os#)#%#s#'##nI#$#4s#PE#$%#5#6#.R+D#$M/#NRQS#KL0R'Q\PN($#JDFE%GKs#+#s#_s#[#s#*#s#[s#_#L[S2*,('DFE\PN-)(Js##BE%GQs#0'N)M#>P%S'#s#1#s#gs#c&##s#cs#g#FnC#$#1s#cD#%###<nO$C$#%s#dL#%#s#&%#1#2#nC#$#3s#e+#%#-##%GDF#s#ms#i#s#8#s#is#m#S#nO$G$#7s#i0#%#&%#8#9#nC#$##s#j5#%#2##nC#$##s#k;#%#9##nI#$#4s#lD#$%#5#6#1Ms#Hs#Ds#CLs#4s#3H)S%s#.s#-J%S'#s#@#s#vs#rs#1##s#rs#v#FnC#$#1s#rD#%###s#+nO$C$#%s#sK#%#s#5%#1#2#nC#$#3s#t)#%#s#C##nC#$##s#us#O#%#s#M##nI#$#4s#vE#$%#5#6#$R/#QS#KLJP$N/#RQS#KLJ1Ms#Vs#Rs#QLDFH\S3s#UEs#Ws#Ss#RDFH#s#~s$&8QnO$G$#7s#~$#%#,%#8#9#nC#$##s$#&#%#s#N##nC#$##s$$s#Z#%#s#X##nI#$#4s$%E#$%#5#6#[S4s#1s#3s#/s#.DFEnO$G$#7s$'##%#@%#8#9=nC#$##s$(s#/#%#s#,##nC#$##s$)s#5#%#s#3##nI#$#4s$*D#$%#5#6#nG#$#&s$+H#-&#4#:#;s#9%#4#<=&#4#<#=3%#>#?1%#@#A1&#@#>#?/%#4#B1'#C#-#D#*s#5&#4#<#E(%#4#<#,S%MNRQS#K&S%Ms#ds#`s#_LDFs#^2s#Ws#V2#s#U&S%Ms#gs#cs#bLs#Ss#Rs#anC#$#3s$1##%#s#\#s#DnC#$##s$2%#%#s#]##nC#$##s$3(#%#s#^##nC#$##s$4s#j#%#*##nI#$#4s$5E#$%#5#6#,MNRQS#KL&MNs#Ds#@s#?JDFE[S,Ms#Es#As#@DFE&MNs#Fs#Bs#AJs#\s#[EnC#$#3s$:##%#s#>#s#4nO$G$#7s$;%#%##%#8#9s#1nC#$##s$<'#%#s#@##nC#$##s$=s#I#%#)##nI#$#4s$>D#$%#5#6#&S%Ms#vs#rs#qLs#bs#aHnC#$#3s$@##%#s#k#s#+nC#$##s$As#w#%#7##nI#$#4s$BE#$%#5#6#,RQS#KLJP,NRQS#KLJ&S%Ms#|s#xs#wLDFH\S-ES%s#}s#ys#xDFHnO$G$#7s$G##%#)%#8#9s#(nC#$##s$H%#%#s#s##nC#$##s$Is$##%#?##nI#$#4s$JE#$%#5#6#[S.Ms#Xs#Ts#SDFEnO$G$#7s$L##%#4%#8#9s#BnC#$##s$M8#%#s#Q##nC#$##s$Ns#Z#%#:##nI#$#4s$OD#$%#5#6#nG#$#&s$PH#-&#4#:#;=%#4#<4&#4#<#=0%#>#?/%#@#A/&#@#>#?.%#4#B/'#C#-#D#*<&#4#<#E(%#4#<#*s$Qs#(#j#1s$/#k#%s$Xs$Sk#&G#k#'S$#k#(S*#k#)I#k#0S+#US5KZJMNRQS#KnC#$##s$[s$$#%#s$*#s#,nC#$##s$\s#1#%#s$+##nC#$##s$]s$7#%#%##nI#$#4s$^E#$%#5#6#ZPNRQS#KLnO$G$#7s$`s#c#%#s#(%#8#9s#VnC#$##s$as#,#%#s#e##nC#$##s$bs#n#%#%##nI#$#4s$cD#$%#5#6#nC#$##s$ds$>#%#,#s#&nI#$#4s$eE#$%#5#6#ZEQS#KLJPZHRQS#KLJnO$G$#7s$hs#J#%#s#*%#8#9s#InC#$##s$is#&#%#s$8##nC#$##s$js$D#%#2##nI#$#4s$kE#$%#5#6#nO$G$#7s$ls#H#%#s#4%#8#9s#bnC#$##s$ms#8#%#s#q##nC#$##s$ns#z#%#1##nI#$#4s$oD#$%#5#6#nG#$#&s$pH#-&#4#:#;4%#4#</&#4#<#=-%#>#?,%#@#A,&#@#>#?+%#4#B,'#C#-#D#*3&#4#<#E'%#4#<#*s$q#s##j#F<#k#<S$s$yk#6S&#k#5S$#k#GS$#k#HS&#k#IS$#US.KnC#$##s$zs$T#%#s#P#@nI#$#4s${E#$%#5#6#nC#$##s$|s$,#%#s#H#=nI#$#4s$}D#$%#5#6#nC#$##s$~s$X#%#s#T#7nI#$#4s%#E#$%#5#6#ZPs$1s$-s$,DFEnO$G$#7s%%##%#s#I%#8#9s#wnC#$##s%&s#M#%#s$*##nC#$##s%'s$3#%#s#O##nI#$#4s%(D#$%#5#6#nG#$#&s%)H#-&#4#:#;,%#4#<*&#4#<#=s#E%#>#?s#D%#@#As#D&#@#>#?s#C%#4#Bs#D'#C#-#D#*s#Q&#4#<#E(%#4#<#*s%*#s#8j#91#k#ES&2VS-FS#j#ES&#[JEs$fs$bs$aDFHnO$G$#7s%0##%#s#N%#8#9s#mnC#$##s%1s#J#%#s$\##nC#$##s%2s$h#%#s#d##nI#$#4s%3E#$%#5#6#nG#$#&s%4H#-&#4#:#;7%#4#<5&#4#<#=s#P%#>#?s#O%#@#As#O&#@#>#?s#N%#4#Bs#O'#C#-#D#*s#\&#4#<#E#%#4#<s#C*s%5#s#Cj#9,#US,KnG#$#&s%8H#-&#4#:#;;%#4#<2&#4#<#=s#T%#>#?s#S%#@#As#S&#@#>#?s#R%#4#Bs#S'#C#-#D#*s#`&#4#<#Es#L%#4#<s#G*s%9#s#Gj#9@#&MNs$Hs$Ds$CJDFs$l6Qs$f2#s$e+S#E2$#&MNs$Ms$Is$HJs$cs$bs$q)Ms$As$\s$[%S'#s$o#s%Is%Es$D##s%Es%I#FnC#$#1s%ED#%###s$ZnO$C$#%s%FL#%#s$d%#1#2#nC#$#3s%G)#%#s$K##nC#$##s%H+#%#s$L##nC#$##s%I0#%#s$M##nC#$##s%Js$V#%#s#r##nI#$#4s%KE#$%#5#6#.Q+D#0Q'S#&NR&$#PDFE%GLs%$#s%Xs%T#s%##s%Ts%X#J[S,N*('DFE&NR+)(Ps$xs$wE)Ns%,s$qP%S'#s%(#s%^s%Zs%*##s%Zs%^#FnC#$#1s%ZD#%###s$onO$C$#%s%[J#%#s$y%#1#2#nC#$#3s%\)#%#+###s%^s%bs$TKnO$G$#7s%^,#%#$%#8#9#nC#$##s%_1#%#.##nC#$##s%`5#%#s#z##nI#$#4s%aD#$%#5#6#&MNs$os$ks$jJs%)s%(H)Ms$cs$~J%S'#s%5#s%ks%gs$f##s%gs%k#FnC#$#1s%gD#%###s$|nO$C$#%s%hL#%#s%*%#1#2#nC#$#3s%i)#%#s$m##nC#$##s%js$v#%#s$6##nI#$#4s%kE#$%#5#6#,QS#KLJPH&MNs$zs$vs$uJDFH\S-EMs${s$ws$vDFHnO$G$#7s%o##%#(%#8#9s$enC#$##s%p%#%#s$t##nC#$##s%qs$}#%#s$=##nI#$#4s%rE#$%#5#6#[S.Ns#)s#'s#&DFEnO$G$#7s%t##%#:%#8#99nC#$##s%us#'#%#s#$##nC#$##s%vs#+#%#s$4##nI#$#4s%wD#$%#5#6#nG#$#&s%xE#-&#4#:#;s#/%#4#<9&#4#<#=/%#>#?.%#@#A.&#@#>#?s$7%#4#B.'#C#-#D#*s$6&#4#<#E(%#4#<#VS:s%y#$KUS2#US;K-s#cs#Hs#E&$#US3&US<K-s#Vs#Ts#L%$#US4)US=K-s#is#hs#Z%$#US6,US>K-s$0s$/s#r%$#US?/US@K-s%fs%es$9%$#\S(2LJPHEDF\S)KLJPHEDF*s&0$#m#&#j#Js&5#(s&6s&3s%us%t#j#Ks&9#(s&:s&4s%zs%y#j#LG#(Gs&5s&#s%~#j#MS$#(S$s&6s&(s&'#j#NS*#(S*s&7s&-s&,#j#OI#(Is&8s&2s&1#j#7S+#(S+s&9s&7s&6#j#Ps&F##"). Qed.
#[export] Hint Rewrite prune1pcB_eqf : bceq.
Lemma prunepcB_eqf : forall fk, prunepcB (mkbc fk) = prunepc fk.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prunepcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prunepc); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kbase); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.br_lookup); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1pc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB_eqf)|] [|@cache; @hints; @kn; @wv; @w; @wa; @x0; @x; @r; @kb; @p; @scs2; @hs2; @kept; @scs1; @hs1; @br2; @cache'; @K; @sp; @e; @o; @IH; @rest; @fk|] "#$t#5#U###$#%#'#&#@#)#(#>#*#-#,#9#A#D#F#+#/#.#=#<#0#T#U#;#B#C#J#M#N#P#R#S#3#2#1#?#I#Q#4#V#W#G#O#E#:#K#H#8#L.#N'#O$#P(#Q&#R&#(%#1)#2)#S$#2+#T)+O+S7(S,S,UP#(K#+#+S-()#(#)k#$&#k#%+#k#&-#k#'K#k#(S&#k#)S'#$CUQ#URC$DVQ#CVRDC$EWQ#DCWREDC$GXQ#EDCXRGEDC$FYQ#GEDCYRFGEDC$I)#JFGEC*IJFGEC'9$#j#&s#$#$JUS8O)$FGED#*JFGED$[Q+JFGE%C[RIJFGE&C,LIJFG'DCVS.s#$#j#*s#(#%s#)s#&'&#j#+s#.#%s#/s#'+*#$L)#IJFGC*LIJFGC's#*$#$S#&OED)$LIJF#*S#LIJF$$N&OGE[Q$S#LIJ#C[RNS#LIJ$C*MNS#LIG(s#;s#9US/JVS0EC#s#>s#<CG$S$VS1#C#Ks#AC#&s#A#E#s#Cs#A%#nP$s#D$#++)#%$#,(##US9s#F#s#Fs#D#DnP$K$#+.-#%$#-%##$S(\S2#S$S%MNLFDVIEFWS3OJDWS3S-FC#s#Ps#J$##s#Js#P#EnH%s#Rs#L$#.s#JD#$%#,#/#nH%s#Ls#R$#+s#K(#$%#.#0#nH%s#Ts#N$#.s#LD#$%#1#2#nH%s#Ns#T$#+s#M+#$%#.#3#nH%s#Ss#Q$#+s#N.#$%#4#5#VS)S$C#Ks#UC#&s#U#E#s#Ws#U%#nP$s#X$#+?=#%$#,<##nP$K$#+@?#%$#-##5\S*S(S$S%MNLFD,S:S4S5S6S(MEFnH%s#Xs#^$#+s#W##$%#.#0/nH%s#`s#Z$#.s#XD#$%#1#2#nH%s#Zs#`$#+s#Y&#$%#.#3#nH%s#_s#]$#+s#Z(#$%#4#5#'s#[/#j#.s#Z#k#4s#bs#]k#%s#e#k#6O#k#'K#k#(S&#k#)S'#k#7S+#US*M[ES$S%MNLFDnH%s#gs#m$#+s#f##$%#.#30nH%s#ls#j$#+s#gs#'#$%#4#5#'s#h#0j#.(#k#8Ks#oUS)MUDC#Ks#rC#&s#r#E#s#ts#r%#nP$s#u$#+s#<s#:#%$#,s#9##nP$K$#+s#=s#<#%$#-##s#2nH%s#ws#u$#+s#r##$%#4#5;'s#s#;j#9,#US/FVS0DC#s#|s#zCEVS)S%C#Ks#~C#&s#~#D#s$$s#~%#nP$s$%$#+s#H(#%$#,'###s$&s$$s#?CnP$K$#+s#J+#%$#-$##\S*S$S%MNS#IGD,S4S5S6S(S$NEFnH%s$&s$,$#+s$%##$%#.#0s#9nH%s$.s$($#.s$&D#$%#1#2#nH%s$(s$.$#+s$'&#$%#.#3#nH%s$-s$+$#+s$((#$%#4#5#VS.s$)#$MUS1#US;M-A@7&$#US2&US<M-s#+s#*s#%%$#))NS#LIG-s$0s#[s#4$#E&OFG\Q,NS#LI#DC,MNS#LI$DC's$6$#m#'#j#*s$;#%s$<s$9s#ds#c#j#+s$A#%s$Bs$:s#js#i#j#:s#n#j#;s$E#j#6O#YS=Os$%s#u#Cj#&s$H#%s$Is$?s$-s$,#j#'K#%Ks$@s$2s$1#j#(S&#%S&s$As$7s$6#j#)S'#%S's$Bs$<s$;#j#7S+#%S+s$Cs$As$@#j#<s$R##"). Qed.
#[export] Hint Rewrite prunepcB_eqf : bceq.

(* [comment removed for export] *)
#[export] Hint Rewrite zf_coversB_eqf kentry_overlayB_eqf kentry_readableB_eqf kn_readableB_eqf kn_overlayB_eqf : bceq.

(* [comment removed for export] *)
Lemma filter_nil_app : forall (l1 l2 : list kentry),
  List.filter is_factb l1 = [] -> List.filter is_factb l2 = [] -> List.filter is_factb (l1 ++ l2) = [].
Proof. intros l1 l2 H1 H2. rewrite List.filter_app, H1, H2. reflexivity. Qed.
Lemma filter_if_single : forall (c : bool) K,
  is_factb K = false -> List.filter is_factb (if c then [K] else []) = [].
Proof. intros c K H. destruct c; cbn; rewrite ?H; reflexivity. Qed.

Lemma kcut_nofacts : forall mk kn wb wk wn kb kk len,
  (forall a n, is_factb (mk a n) = false) ->
  List.filter is_factb (kcut mk kn wb wk wn kb kk len) = [].
Proof.
  intros mk kn wb wk wn kb kk len H. unfold kcut.
  apply filter_nil_app.
  - apply filter_if_single. apply H.
  - match goal with |- List.filter is_factb (if ?c then _ else _) = [] => destruct c; [|reflexivity] end.
    destruct (split_lit (mkAlu ALU_ADD (mkAlu ALU_ADD wb (ELit wk)) wn)) as [hb ho].
    cbn [List.filter]. rewrite H. reflexivity.
Qed.
Lemma ktrim_nofacts : forall mk kb kk l0 k w,
  (forall a n, is_factb (mk a n) = false) ->
  List.filter is_factb (ktrim mk kb kk l0 k w) = [].
Proof. intros. unfold ktrim. apply filter_nil_app; apply filter_if_single; apply H. Qed.
Lemma kword_cut_nofacts : forall kb kk w' v k w, List.filter is_factb (kword_cut kb kk w' v k w) = [].
Proof.
  intros. unfold kword_cut. destruct v; try reflexivity.
  apply filter_nil_app; apply filter_if_single; reflexivity.
Qed.
Lemma prune_zf_nofacts : forall mk allkn wb k w K kb kk len apart hints diffbase,
  (forall a n, is_factb (mk a n) = false) -> is_factb K = false ->
  List.filter is_factb (fst (fst (diffbase tt))) = [] ->
  List.filter is_factb (fst (fst (prune_zf mk allkn wb k w K kb kk len apart hints diffbase))) = [].
Proof.
  intros mk allkn wb k w K kb kk len apart hints diffbase Hm HK Hd. unfold prune_zf.
  destruct (expr_eqb kb wb).
  - destruct len; cbn [fst]; try (apply ktrim_nofacts; exact Hm);
      (destruct (Z.leb (k + Z.of_nat w) kk); cbn [fst List.filter]; [rewrite HK; reflexivity | apply kcut_nofacts; exact Hm]).
  - destruct (apart tt); cbn [fst List.filter]; [rewrite HK; reflexivity|].
    destruct (kcut mk allkn wb k (elen w) kb kk len) as [|c cs] eqn:E; [exact Hd|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. exact Hm.
Qed.

Ltac nfcrush :=
  cbn [fst List.filter is_factb];
  first [ reflexivity
        | apply kword_cut_nofacts
        | (apply filter_nil_app; apply filter_if_single; reflexivity)
        | match goal with
          | |- context [if ?c then _ else _] => destruct c; nfcrush
          | |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; nfcrush
          | |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; nfcrush
          | |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; nfcrush
          end ].

Lemma prune1p_facts : forall allkn sp wa w wv K hints,
  List.filter is_factb (fst (fst (prune1p allkn sp wa w wv K hints))) = List.filter is_factb [K].
Proof.
  intros allkn sp wa w wv K hints. unfold prune1p.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [List.filter is_factb];
    try reflexivity;
    try (apply prune_zf_nofacts; [reflexivity|reflexivity|]); nfcrush.
Qed.

Lemma prune1pc_facts : forall allkn sp wa w wv K hints br2,
  List.filter is_factb (fst (fst (prune1pc allkn sp wa w wv K hints br2))) = List.filter is_factb [K].
Proof.
  intros allkn sp wa w wv K hints br2. unfold prune1pc.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try apply prune1p_facts.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kzero_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut KZero allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kfill_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut (fun a n => KFill a n c) allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kunk_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut KUnk allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
Qed.

Lemma prunepc_facts : forall allkn sp wa w wv kn hints cache,
  List.filter is_factb (fst (fst (prunepc allkn sp wa w wv kn hints cache))) = List.filter is_factb kn.
Proof.
  intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache; [reflexivity|].
  cbn [prunepc].
  destruct (match kbase K with Some kb => match br_lookup cache kb with Some r => (r, cache) | None => (base_range allkn kb, (kb, base_range allkn kb) :: cache) end | None => (None, cache) end) as [br2 cache'].
  destruct (prune1pc allkn sp wa w wv K hints br2) as [[kept scs1] hs1] eqn:E1.
  destruct (prunepc allkn sp wa w wv rest hs1 cache') as [[r scs2] hs2] eqn:E2.
  cbn [fst]. rewrite List.filter_app. pose proof (prune1pc_facts allkn sp wa w wv K hints br2) as H1. rewrite E1 in H1. cbn [fst] in H1.
  rewrite H1. specialize (IH hs1 cache'). rewrite E2 in IH. cbn [fst] in IH. rewrite IH. cbn [List.filter]. destruct (is_factb K); reflexivity.
Qed.

Lemma carry_facts : forall log kn hints,
  List.filter is_factb (fst (fst (carry log kn hints))) = List.filter is_factb kn.
Proof.
  intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry]. destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in IH.
  destruct (prunepc _ _ _ _ _ kn1 hs1 []) as [[kn2 scs2] hs2] eqn:E.
  cbn [fst List.filter is_factb]. pose proof (prunepc_facts (facts_of kn1) (mk_sprep (facts_of kn1) (a_base a) (a_off a) (elen w)) a w v kn1 hs1 []) as H.
  rewrite E in H. cbn [fst] in H. rewrite H. exact IH.
Qed.

Fixpoint carryB (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carryB bc older kn hints in
      let '(kn2, scs2, hs2) := prunepcB bc (mk_sprepB bc (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Lemma carryB_eq : forall log kn hints, carryB (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.carryB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.facts_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.carry); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__4); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prunepcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KWord); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prunepc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mk_sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.carry_facts); constr:(@Stdlib.Lists.List.filter); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.is_factb); constr:(@Corelib.Init.Datatypes.fst); constr:(@kc__2); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prunepcB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.facts_of_filter); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SE); constr:(@kc__2 ((@Corelib.Init.Datatypes.list) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry)) ((@Corelib.Init.Datatypes.list) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond))); constr:(@kc__2 ((@Corelib.Init.Datatypes.prod) ((@Corelib.Init.Datatypes.list) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry)) ((@Corelib.Init.Datatypes.list) (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond))) ((@Corelib.Init.Datatypes.list) (@Corelib.Init.Datatypes.bool)))|] [|@log; @l; @s; @p; @kn2; @scs2; @x; @hs2; @kn1; @scs1; @hs1; @HF; @IH; @cache; @hints; @kn; @wv; @w; @wa; @sp; @n1; @k1; @b1; @older; @v; @a; @e_val; @e_width; @e_addr; @a0|] "#&&#;#e#$#D###%#@#2#'#&#4#3#,#`#(#0#-#?#+#P#/#.#1#6#E#7#X#*#5#8#9#O#N#K#J#d#\#]#S#R#g#c#b#A#W#^#:#e#f#h#L#B#C#Y#H#G#_#F#I#a#M#>#T#U#V#Z#Q#[8#U&#V'#W$#X$#Y&#Z'#[&#E+#\&#]&#F'#G'#^$#_$#`$#a$#H+#b&#c)#$%#d&/R/G/S</S)6%#6#%%F&#(#EFC)EFC#'$#j#$-#US2R)#CEVS3+#%I&#(#EIJ)EIJ#0$#%O&#,RFC($#OI)$OI#6$#k##)#k#%=#j#&R#%M&#(#EMS#)EMS##>$#)CQM%H&#0M1M2S#.&%$#6S+S+US=#6S$#US2#3+'MS#S,CF#4PS%S&,G#C7S)IE$s#2s#0$#$s#0s#2#FnD%s#4s#2$#'s#0C#$%#(#)#nD%s#2s#4$#*s#1)#$%#'#+#nD%s#6s#4$#'s#2C#$%#,#-#nD%s#4s#6$#*s#3E#$%#'#.#)FS&Q%C-#654*$#MS#S,CF0nD%s#9s#;$#*s#8##$%#'#+*nD%s#=s#;$#'s#9C#$%#,#-#nD%s#;s#=$#*s#:(#$%#'#.##s#;*#j#'s#<#WS>CQM+s#?s#AA+s#Cs#A#'GN#'GNQ#s#F$#%P&#(#IPS%#s#F#E+s#Hs#JC+s#Ls#J#'GN#'GNS'#s#O$#%S(&#0P1P2S%.&%$#3'#PS%S&CFs#+4KLH,G#C$s#Ys#W#s#*$s#Ws#Y#FnD%s#[s#Y$#'s#WC#$%#(#)#nD%s#Ys#[$#*s#X(#$%#'#+#nD%s#]s#[$#'s#YC#$%#,#-#nD%s#[s#]$#*s#ZF#$%#'#.#-s#(/.-*s#)#PS%S&CFs#5nD%s#^s#`$#*s#]##$%#'#+(nD%s#bs#`$#'s#^C#$%#,#-#nD%s#`s#b$#*s#_F#$%#'#.##s#`(#k#/8#k#0>#j#'s#c#%K&#(#S#KL$s#hs#jCE#s#h$#$s#js#lFC+s#ks#m#+s#os#m#'GN#'GNS-#s#r$#%S.&#0H1H2S'.&%$#3'#HS'PCIs#N4S(S-K,G#C$s#|s#z#s#M$s#zs#|#FnD%s#~s#|$#'s#zC#$%#(#)#nD%s#|s#~$#*s#{(#$%#'#+#nD%s$$s#~$#'s#|J#$%#,#-#-s#J.-,*s#K#HS'PCIs#WnD%s$$s$&$#*s$###$%#'#+'nD%s$(s$&$#'s$$J#$%#,#-##s$%'#k#/6#k#0=#k#%s$+#j#'s$*#%S*&#(#S&S*S($s$1s$/FC$s$/s$1#E#s$/%#$s$4s$2JF$s$2s$4#C+s$3s$5#+s$7s$5#'GN#'GNS.#s$:$#'GNS/&E0K1K2L.&%$#3'#KLHOJs#r4S.S*S(,G#C7S)S#E$s$Es$C$#$s$Cs$E#FnD%s$Gs$E$#'s$CC#$%#(#)#nD%s$Es$G$#*s$D)#$%#'#+#-s$6.-,*s$7#KLHOJs#{nD%s$Hs$J$#*s$G##$%#'#+&#s$H&#j#%s$M#'GNI'GNS?&#.#6543$#KLHOJs$'nD%s$Ps$R$#*s$O##$%#'#+.-E987*E#KLHOJs$*nD%s$Ss$U$#*s$R##$%#'#+1#s$S&#j#%s$X#'GNO-#?>=*$#KLHOJs$0nD%s$Ys$[$#*s$X##$%#'#+7#s$Y7#j#%s$^##s$[9+j#%s$`#/s$7k#1#s$^k#2s$b#k#3s$d#k#4S$#k#5S0#k#6S1#k#7S4#US5s$[.s$Vs#/s#.s#-[E#KLHOJs$@nD%s$is$k$#*s$h##$%#'#+s#'#s$i#s#$j#'(#k#8S$S4k#9S+#k#:S$#US6s$dWEs#8s#7s#6*s$a#KLHOJs$InD%s$rs$t$#*s$q##$%#'#+s#0#s$r#s#-j#&(#0L1L2H-s$m%$#*s$n#LHS'IFs$Q4S*S(S-,G#C7S)S,E$s%$s$~$#$s$~s%$#FnD%s%&s%$$#'s$~C#$%#(#)#nD%s%$s%&$#*s%#)#$%#'#+#VS3s%$#US7s$vUS@s$x5872%$#US8s$yUSAs${5s#$s##>%$#US9IZS:s%0s$~s#.$s#@#ZS:s%1s#As#1#s#TE5s%2s#Bs#8#s%$%%S/US9S/5s%5s#Xs#F%$#j#/s#Z#j#0s#b#j#.s%7#j#-s%7#j#,s%:#V#CEj#%s%:#j#%s%=#YS;s%>s%<s#o#Ej#'s%<#V#CEj#%s%@#j#'s%?#YS;s%@s%Bs$:#EV#FCl#'s$ks%A#l#/s$cs$^#%Q&#(#CQM5s%Fs%)s$h&#EWSBIJF,R#C('#QM)$QM#s%K$#m#(#j#0s%1#j#;s%S#j#<S$#j#5S0#j#=S1#W#FCEj#>S$#j#?S0#j#@S1#WSCs%?#Ej#AR#YSDRs%Rs%O#Fj#2s%\#j#3s%^#j#$s%`##"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
  induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?p_aluop_eqb_refl, ?p_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma p_prune1pc_eq : forall allkn sp wa w wv K hints br2,
  match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
  prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
  intros allkn sp wa w wv K hints br2 Hb.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in Hb; try reflexivity; subst br2; unfold prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    destruct (expr_eqb kb (a_base wa)); reflexivity.
Qed.
Definition p_br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
  Forall (fun p => snd p = base_range allkn (fst p)) c.
Lemma p_br_lookup_ok : forall allkn c b r, p_br_cache_ok allkn c -> br_lookup c b = Some r -> r = base_range allkn b.
Proof.
  intros allkn c b r Hc. induction c as [|[b' r'] rest IH]; cbn; [discriminate|].
  apply Forall_cons_iff in Hc as [H1 Hc]. cbn in H1.
  destruct (expr_eqb b b') eqn:E.
  - intros H. injection H as <-. apply p_expr_eqb_eq in E. subst b'. exact H1.
  - apply IH. exact Hc.
Qed.
Lemma p_prunepc_eq : forall allkn sp wa w wv kn hints cache,
  p_br_cache_ok allkn cache ->
  prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints.
Proof.
  intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
  cbn [prunepc prunep].
  destruct (kbase K) as [kb|] eqn:HK.
  - destruct (br_lookup cache kb) as [r|] eqn:HL.
    + rewrite (p_prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (p_br_lookup_ok _ _ _ _ Hc HL)).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
    + rewrite (p_prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
      rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
  - rewrite (p_prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
    destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
Qed.

(* [comment removed for export] *)
Definition g1 (fk : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) : list kentry :=
  fst (fst (prune1p fk sp wa w wv K [])).

Ltac pk_crush :=
  cbn [fst snd];
  first [ reflexivity
        | match goal with
          | |- context [if ?c then _ else _] => destruct c; pk_crush
          | |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; pk_crush
          | |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; pk_crush
          | |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; pk_crush
          end ].

Lemma prune1p_nil : forall fk sp wa w wv K,
  prune1p fk sp wa w wv K [] = (g1 fk sp wa w wv K, [], []).
Proof.
  intros. unfold g1, prune1p, prune_zf.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len]; pk_crush.
Qed.
Lemma prunep_nil : forall fk sp wa w wv kn,
  prunep fk sp wa w wv kn [] = (flat_map (g1 fk sp wa w wv) kn, [], []).
Proof.
  intros fk sp wa w wv kn. induction kn as [|K rest IH]; [reflexivity|].
  cbn [prunep flat_map]. rewrite prune1p_nil, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive pk_res := PKeep | PRepl (l : list kentry).
Definition pk_list (K : kentry) (r : pk_res) : list kentry := match r with PKeep => [K] | PRepl l => l end.

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition prune1pcK (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
         | cut => PRepl cut
         end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
  | KImg lo hi =>
      match wb with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          PRepl (r1 ++ r2)
      | _ => if Z.ltb (hi - lo) (two64) then
               (if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%lzb then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%lzb then PKeep
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := (l0 mod two64)%Z in
                     if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%lzb then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
  end.
Local Close Scope lzb_scope.
Scheme kc__6 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry Sort Prop.
Scheme kc__7 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__8 := Elimination for Corelib.Init.Datatypes.list Sort Prop.
Scheme kc__9 := Elimination for Corelib.Numbers.BinNums.Z Sort Prop.

Lemma prune1pcK_eq : forall fk sp wa w wv K br2 same,
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kbase); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@Corelib.Init.Logic.True); constr:(@kc__6); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.pk_list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1pc); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__5); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_pc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.pk_res); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.PKeep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.PRepl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kword_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@Stdlib.Arith.PeanoNat.Nat.eqb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_p); constr:(@Corelib.Init.Datatypes.andb); constr:(@kc__7); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pcB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KZero); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ktrim); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kcut); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EVar); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EAlu); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EAluw); constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EMd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EMdw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EExt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EBlob); constr:(@kc__8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KBlob); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KImg); constr:(@Corelib.Init.Datatypes.app); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@kc__9); constr:(@Corelib.Numbers.BinNums.positive); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KAlign); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KRange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KDisj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KFill); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KUnk); constr:(@kc__8 (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry))|] [|@x; @kb; @H; @k; @v; @w; @s; @same; @n2; @k2; @b2; @br2; @n1; @k1; @b1; @sp; @apart; @b; @w'; @kk; @a_off; @a_base; @a; @n; @len; @l0; @op; @sx; @lo; @e; @k0; @i; @l; @wn; @wk; @wb; @mk; @z; @len2; @len1; @bk; @p; @lo0; @e2; @e1; @hi; @m'; @e'; @m; @hi'; @lo'; @en; @ek; @eb; @m2; @c2; @m1; @c1; @a2; @a1; @c; @fc; @K; @wv; @wa; @fk|] "#SK#A$A#M#I###`#f#E#L#$#%#&#'#H#(#)#*#D#0#+#1#4#.#,#-#3#5#6#/#2#~$%#G#w$C#e#7#m#J#A#R#8#<#:#>#;#9$;#u$2$@#K#Z#F#_#z$*#y#=#X#v$+$/$-#q$<$>$?$A#@#k#l#}$#$$$&$'$($)$1$.$9$=#S#W#o#O#T#g#p#t$B#s$3#Q$4$,#d#r#U#Y#a#n#b#{#N#P#]#i$5#c#^#V#x#|$:#\#j$6$7$8#[$0#hU#u&#v'#w&#x%#y$#z&#{%#X+#|&#}'#~%#a+$#$$$&$%&$&$$'%#B%#C%$(+$)+$*%$+%$,%$--$.$$/%$0%$1$#Z+$2%$3$#W,$4)$5$$6)$7$$8($9&$:%$;%$<%$=%$>&$?$$@)#**#,*#-*#b+URHVSDIIUS7#<K/P=E#%CJ#nS7$D$#$S8&#%$#%##S9<E/S$=E#%CL#nS7$D$#$S8&#%$#%##S9ES)6#S(S$QPJLM&J#URSLVSD3#URCUSEC7S)S(S$QPJ#M#&%##8(#%9*#k#&.#j#'H#IKJE<#/S%=E#%CS(#nS7$D$#$S8&#%$#%##S9ILKJES*6#S.S%S#S-$S(S)&%#7S*S.S%S#S-&3S)#65##s#(8#%s#)&#k#&+#k#(D#k#)N#j#*S1#>LKI#JE<#/S&=E#%CS-#nS7$D$#$S8&#%$#%##S9=M&>OMI#LKES56#S,S+S&S*$ES%&%#7S5S,S+S&S*&s#(S%#s#+s#*##s#=s#-#%s#>&#j#+C#k#,DCk#-I#k#.D#k#/s#A#k#0D#k#1I#k#2D#k#3SF#USGS,/S+=O#BL:M#2S+8$#BS&:%#8#MnC#$##C&#%#S4##POMLK(S&'#nC#$##F%#%#G##?S&?L\ES,1-$S%OM#USWSXJS&#JL$nC#$##C$#%###S6=S*KnC#$##C$#%###S6USEH'#nC#$##F+#%#G##nC#$##F&#%#G##nC#$##F-#%#G##nC#$#+F<#%#1##&s#0#VSDs#Us#T9;8(Hs#3+USESL$s#js#Z$#$s#Zs#Y#s#X$s#ls#\;%$s#\s#[#s#ZnC#$##*)#%#%##.S5S,s#(s#$;OM:3873#6/s#>2s#?.S5S,s#-s#)@$#?$s#us#e8.$s#es#d#s#cnC#$#43%#%#.##nC#$##4)#%#/##nC#$##5,#%#0##nC#$##6s#2#%#.##CS5S,s#4s#0s#'S%OMs#&CS5S,s#5s#1s#(S%,+s#'nC#$#49##%#4#)nC#$##:/#%#5##nC#$##;&#%#6##nC#$##<s#8#%#(###s#ps#o##s$&s#r#%s$'@#j#5s#?#>POI#MLBM:O#2S,8$#BS+:%#8#OnC#$##C&#%#S4##PPOML(S+'#nC#$##F%#%#G##/S,?S+?MCS:S5%.$S.PO#JS+s#?JMs#@nC#$##C$#%###S6=S&LnC#$##C$#%###S6nC#$##F(#%#G#s#=nC#$##F$#%#G##nC#$##F*#%#G##nC#$#+FE#%#/##&;#985(H=s#D$s$Fs$6#s#;$s$6s$5#s$4$s$Hs$87s#=$s$8s$7#s$6nC#$##s#B(#%#%##.S:S57@6PO53433#2nC#$#4s#F%#%#)#s#6nC#$##s#G$#%#*##nC#$##s#H'#%#+##nC#$##s#IE#%#)##nC#$#4s#J;#%#-#s#:nC#$##s#K(#%#.##nC#$##s#L=#%#/##nC#$##s#ME#%#&###s$Es$D##s$Ws$G#%s$X7#j#5C#>QPI#OM2S5BS,:$#8#PnC#$##CE#%#S4##PQPOM'S,'#nC#$##F%#%#G##&+#9E((H-s#e$s$gs$W#s#\$s$Ws$V#s$U$s$is$Y*s#^$s$Ys$X#s$WnC#$##s#c(#%#%###s$[s$Z##s$ms$]#%s$n,#j#5C#9S4s#AnC#$##s#i##%#s#,#s#*#s$as$`##s$ss$c#)s$t#&s#MG%s$v#%m#%#>S$QI#PO2S:PS$QPO#S5'#nC#$##FE#%#G##&'#9S6E(H)s$#$s%%s$q#s#v$s$qs$p#s$o$s%'s$s*s#x$s$ss$r#s$qnC#$##s#}(#%#%###s$us$t##s%+s$w#%s%,,#j#5C#9S6S4nC#$##s$'##%#s#%#s###s${s$z##s%1s$}#)s%2#&s#6G%s%4#%m#%#9S6S6nC#$##s$/##%#s#-#s#+#s%'s%&##s%9s%)#)s%:#&s#>s#7%s%<#%m#%#,3+#El#5s#lC#nC#$##Fs#m#%#G#s#j&s#u#9S6s#onC#$##s$;##%#s#Z#s#X#s%3s%2##s%Es%5#%s%F'#m#*#,s#7s#/#El#5s$YC#&s$qs$S#s%:s%9s$;#s%Ls%<#%s%M%#m#'#JS,s$TJOs$UnC#$##C$#%###S6=S+MnC#$##C$#%###S6nC#$##FE#%#G#s$RnC#$##F$#%#G##nC#$##FE#%#G##&s#Z#3+*3#)nC#$#4s$RE#%#s#P#s$BnC#$##s$S$#%#s#Q##nC#$##s$TE#%#s#R###s%Ls%K##s%^s%N#%s%_*#j#5C#)s%as#z#s%Qs%Ps#y#s%cs%S#%s%ds#M#m#&#JPs$knC#$##CE#%###S6=S,OnC#$##C$#%###S6nC#$##F##%#G#s$h&s#P#3E(3#'nC#$##s$f##%#s#J#s$V#s%^s%]##s%ps%`#%s%q(#j#5C#>S(S$I#QP=S5PnC#$##CE#%###S6nC#$##F##%#G#s$u&&#3S4E3#'(H)s$z$s%|s%l#s$q$s%ls%k#s%jnC#$##s$v&#%###s$f#s%ns%m##s&$s%p#%s&%+#j#5C#>S)S(I#S$Q&#s#33S4S43#E(H&s%+$s&-s%y#s$~$s%ys%x#s%wnC#$##s%'&#%###s$s#s%{s%z##s&1s%}#%s&2+#j#5C#3,S4nC#$##s%-##%#6#s$y#s&%s&$##s&7s&'#)s&8#&s##G%s&:#%m#%#34S6nC#$##s%5##%#>#s%%#s&-s&,##s&?s&/#)s&@#&s#+s%?%s&B#%m#%#,3+#El#5s#;C#nC#$##Fs#<#%#G#s%D&s$,#3@s#>nC#$##s%A##%#s$%#s%1#s&9s&8##s&Ks&;#%s&L'#m#*#3S4S63#s#EnC#$##s%H##%#s$,#s%8#s&@s&?##s&Rs&B#)s&S#&s$9s%R%s&U#%m#%#,s#3,#El#5s#fC#nC#$##Cs#g#%#s#e#S6nC#$##F##%#G#s%X&s$^#3S4s#j3#s#inC#$##s%V##%#s$T#s%F#s&Ns&M##s&`s&P#%s&a(#m#,#3S6s#q3#s#pnC#$##s%]##%#s$[#s%M#s&Us&T##s&gs&W#)s&h#&s$ls%g%s&j#%m#%#,s#X,#El#5s%5C#nC#$##Fs%2#%#G#s%l&s%G#nC#$##s%hs%%#%#s%+#s%X#s&`s&_##s&rs&b#%s&s&#m#)#,s#ss#n#El#5s%YC#nC#$##Fs%Z#%#G#s%unC#$##Fs%x#%#G##nC#$##Fs%\#%#G##&s&E#nC#$#4s%ss%^#%#s%n#s%cnC#$##s%ts%i#%#s%o##nC#$##s%us%`#%#s%p###s&ms&l##s'#s&o#%s'$(#m#-#,s%+s$6#El#5s&PC#>MLI#KJBK:L#2S&8$#BS*:%#8#LnC#$##C&#%#S4##PMLKJ(S*'#nC#$##F%#%#G##?S*?KCS,S+s&d-$S#ML#JS*s&=JKs&>nC#$##C$#%###S6=S.JnC#$##C$#%###S6nC#$##F(#%#G#s&;nC#$##F$#%#G##nC#$##F*#%#G##nC#$#+Fs&i#%#.##&:#974(H<s&B$s'Ds'4#s&9$s'4s'3#s'2$s'Fs'66s&;$s'6s'5#s'4nC#$##s&@(#%#%##.S,S+s&v?6ML53433#2nC#$#4s&D%#%#)#s&4nC#$##s&E$#%#*##nC#$##s&F'#%#+##nC#$##s&Gs&x#%#)##nC#$#4s&H;#%#-#s&8nC#$##s&I(#%#.##nC#$##s&J=#%#/##nC#$##s&Ks&|#%#&###s'Cs'B##s'Us'E#%s'V7#m#s#2#/s#22s#3.S,S+s'+s#0s#'$#s#&nC#$#4s&S##%#8#s&CnC#$##s&T3#%#9##nC#$##s&U6#%#:##nC#$##s&Vs'+#%#8##CS,S+s'0s#5s#,S#)(s#+nC#$#4s&X##%#=#s&HnC#$##s&Y8#%#>##nC#$##s&Zs#-#%#?##nC#$##s&[s'0#%#'###s'Ss'R##s'es'U#%s'fs#'#m#2#ES,USA#USMS,Ds'&s'%s&E&$#]SA&S+s'=s#Bs#9S#MLs#8nC#$##F##%#G#s&knC#$##Fs#4#%#G##nC#$##F%#%#G##nC#$#+Fs'=#%#s#>##&s#J#%s'r#/m#*#6.S+S&S*S.s#Ms'AS#&s#N#7S,S+S&S*S.s#Os'cS##s'fs'e##s'xs'h#%s'y&#m#)#DCs'Hs'>#S-Ej#&s'J#j#(D#j#6N#j#7I#j#%D#V#JEj#8I#j#9D#Ns'Y#Ej#:S1#W#KJEj#(D#j#)N#j#:S1#4JE<#/S-=E#%CQ#nS7$D$#$S8&#%$#%##S94KJES%6#S#S-S'S)$QS$&%#7S%S#S-S'S)&s(%S$#s((s('##s(:s(*#%s(;&#k#&+#k#;D#j#*S1#>KJ4#E<#/S.=E#%CS)#nS7$D$#$S8&#%$#%##S9=L&4s#}KES+6#S&S*S.S%$ES-&%#7S+S&S*S.S%&s(8S-#s(;s(:##s(Ms(=#%s(N&#j#+C#USGS&/S*=M#FS2OMEs$)S*'#8s$(M@s#LS2s('s$,s$#OML'#nC#$##F%#%#G##8s'+PES:@#S2s''s'0s'&QPO'#nC#$##F&#%#G##8s&^QES?/S5?S,@%S2$s&d#S$QP'#nC#$##F(#%#G##nD#$#<FK#+$#=3$#;/&#>#:#5*&#>#:#5*&#>#:#5*&#>#:#5*'#?#@#;#A#'#?#B#C#;#2S*?S.\ES&9$#S-MLK@s##S2:%$MLKnC#$##F$#%#G#s'h(HJE'#nR$H$#$F&#%#%%#B#D#nC#$##F(#%#G##nC#$#+F?#%#,##&s#+#$s(qs(a@s'f$s(as(`#s(_4s(?L(H#s's$s(us(e#s'j$s(es(d#s(c*S2S,s(Hs$Ms$DOML$s(xs(h#s'm$s(hs(g#s(fnC#$##s'rs#'#%#&##4s'#O(H#s'{$s(}s(m#s'r$s(ms(l#s(k*S2S:s'Ks'Ts'JQPO$s)$s(p#s'u$s(ps(o#s(nnC#$##s'zs#+#%#&##4s&iP(H#s('$s))s(u#s'z$s(us(t#s(s*S2S?s#)s'-s#(S$QP$s),s(x#s'}$s(xs(w#s(vnC#$##s(&s#.#%#&##nD#$#<s('K#+$#=;$#;3&#>#:#5+&#>#:#5+&#>#:#5+&#>#:#5+'#?#@#;#A#'#?#B#C#;#.S+S&s#=s#(s#'MLK(Hs#Hs(0$s)2s(~#s('$s(~s(}#s(|*S2S+s#As#,s#+MLK.S+S&s#Bs#-s#,s$;s$:KnC#$#4s(.##%#%#s'z$s)7s)'s#*s(,$s)'s)&#s)%nR$H$#$s(1'#%#%%#B#D#nC#$##s(2,#%#)##nC#$##s(3s#G#%#.##CS+S&s#Is#4s#3S-MLKCS+S&s#Js#5s#4S-s$Cs$BKnC#$#4s(6##%#-#s(&nR$H$#$s(7-#%##%#B#D)nC#$##s(8&#%#/##nC#$##s(9s#M#%#(###s)1s)0##s)Cs)3#%s)Ds#2#j#5s(\#k##DHk##S1#k#<Ds)Hk#7I#k#%D#k#ED#k#FI#k#GD#k#H)#VSHES+j#H+#QS2s(~s%'s$zOML'#nC#$##Fs#\#%#G##RS2s'|s()s'{QPO'#nC#$##Fs#[#%#G##SS2s#Us'Ys#TS$QP'#nC#$##Fs#Y#%#G##nD#$#<FK#+$#=s#d$#;)&#>#:#5&&#>#:#5&&#>#:#5&&#>#:#5&'#?#@#;#A#'#?#B#C#;#[ES2s#hs#Ss#RMLKnC#$##FB#%#G#s(ZnR$H$#$F$#%##%#B#Ds#OnC#$##Fs#$#%#G##nC#$#+Fs#k#%#'##&s#w#%s)a#@j#D6#FS2POEs(tS&'#8s(sO*S2S5s({s(ws(nPOM'#nC#$##F%#%#G##'s#@nC#$##Fs#j#%#G##BS5:s'P#8#S$/S:?S5*S2S<$s'T#S(S$Q'#nC#$##F'#%#G##nD#$#<FL#+$#=1$#;-&#>#:#5+&#>#:#5+&#>#:#5+&#>#:#5+'#?#@#;#A#'#?#B#C#;#CS,S+s)Es%Js%AS#OMLnC#$##F##%#G#s(snR$H$#$Fs#]#%##%#B#Ds#hnC#$##F%#%#G##nC#$#+FE#%#'##&s#d#$s)zs)j9s(o$s)js)i#s)h4s(UM(H#s(|$s)~s)n#s(s$s)ns)m#s)l$s*$s)p<s(u$s)ps)o#s)nnC#$##s(z?#%#%##4s&nQ(H#s)'$s*)s)u#s(z$s)us)t#s)s$s*+s)w9s(|$s)ws)v#s)unC#$##s)%>#%#%##nD#$#<s)&L#+$#=1$#;*&#>#:#5s#^&#>#:#5s#^&#>#:#5s#^&#>#:#5s#^'#?#@#;#A#'#?#B#C#;#.S,S+s)\s%as%XOMLnC#$#4s)(##%#s#t#s(tnR$H$#$s))s#t#%##%#B#Ds#WnC#$##s)*%#%#s#v##nC#$##s)+E#%#'##nC#$#4s),>#%#s#x#s(xnR$H$#$s)-s#x#%##%#B#Ds#[nC#$##s).@#%#s#z##nC#$##s)/E#%#&###s*'s*&##s*9s*)#%s*:?#j#5C#BS.:s$5#8#LFS2QPEs(pS+'#'s#|nC#$##FJ#%#G##nC#$##FL#%#G#s#0/S?2S??S:*S2S>%$#S)S(S$'#nC#$##FM#%#G##nD#$#<FM#+$#=,$#;*&#>#:#5)&#>#:#5)&#>#:#5)&#>#:#5)'#?#@#;#A#'#?#B#C#;#&s#-#$s*Ls*</s)A$s*<s*;#s*:nC#$##s)FJ#%#s$.#s$+nC#$##s)GL#%#s#'#s#%4s'+S$(H#s)P$s*Rs*B#s)G$s*Bs*A#s*@$s*Ts*D/s)I$s*Ds*C#s*BnC#$##s)NM#%#%##nD#$#<s)OM#+$#=,$#;+&#>#:#5*&#>#:#5*&#>#:#5*&#>#:#5*'#?#@#;#A#'#?#B#C#;##s*Gs*F##s*Ys*I#%s*Z1#j#5C#4s)5EnD#$#<FE#+$#=?$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&$#4s(cJ(H#s)_$s*as*Q#s)V$s*Qs*P#s*O4s'NL(H#s)c$s*es*U#s)Z$s*Us*T#s*S4s'BM(H#s)g$s*is*Y#s)^$s*Ys*X#s*WnD#$#<s)cE#+$#=@$#;+&#>#:#5'&#>#:#5'&#>#:#5'&#>#:#5''#?#@#;#A#'#?#B#C#;##s*[s*Z##s*ms*]#%s*n2#j#AD#)s*ps#3GE4s(v#&#s#5#s*cs*bs#)#s*us*e#%s*v%#m#)#j#II#U#Ej#II#USYE4s)$#(H#s)|)s*~#&%G$s+$s*p%s)u$s*ps*o#s*n#s*qs*p##s+'s*s#%s+('#m#)#j#;N#U#Ej#;N#>S'S)WSZKJE4$#(H#s*/)s+1#&%G$s+3s+#%s*($s+#s*~#s*}#s+$s+###s+6s+&#%s+7'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#WS[KJE46#(H#s*A)s+C#&%G$s+Es+5%s*:$s+5s+4#s+3#s+6s+5##s+Hs+8#%s+I'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#WS\KJE4s#(#(H#s*S)s+U#&%G$s+Ws+G%s*L$s+Gs+F#s+E#s+Hs+G##s+Zs+J#%s+['#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#WS]KJE4s#:#(H#s*e)s+g#&%G$s+is+Y%s*^$s+Ys+X#s+W#s+Zs+Y##s+ls+\#%s+m'#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#>S#S-XS^LKJE4$#(H#s*x)s+z#&%G$s+|s+l%s*q$s+ls+k#s+j#s+ms+l##s,#s+o#%s,$'#m#)#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#XS_LKJE48#(H#s+0)s,2#&%G$s,4s,$%s+)$s,$s,##s+~#s,%s,$##s,7s,'#%s,8'#m#)#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s$2s$'s#us#bs#Ps#>s#,7#LnD#$#<FL#+$#=s%>$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&s&0#nD#$#<s+>L#+$#=s%)$#;s%%&#>#:#5s%z&#>#:#5s%z&#>#:#5s%z&#>#:#5s%z'#?#@#;#As$z'#?#B#C#;s$z#s,6s,5##s,Hs,8#%s,I&#m#)#*S2S:s*ss*|s*rQPJ'#*S2S<s%=s*1s%<S(S$L'#*S2S>s$is$hs$gS)S(M'#nD#$#<FE#+$#=s$o$#;'&#>#:#5%&#>#:#5%&#>#:#5%&#>#:#5%'#?#@#;#A#'#?#B#C#;#&s$T#$s,Ss,C*s+H$s,Cs,B#s,A$s,Us,E*s+J$s,Es,D#s,C$s,Ws,G*s+L$s,Gs,F#s,EnD#$#<s+QE#+$#=s$j$#;'&#>#:#5%&#>#:#5%&#>#:#5%&#>#:#5%'#?#@#;#A#'#?#B#C#;##s,Is,H##s,[s,K#%s,\,#j#AD#*S2S:s+*s+3s+)QPs$A)s,_#'$&s$C#$s,bs,R&s+W$s,Rs,Q#s,P#s,Ss,R##s,es,U#%s,f'#m#*#j#;N#U#Ej#;N#/S<2S<?S?*S2S;%$#S'S)s$B)s,o#'$&s$D#$s,rs,b&s+g$s,bs,a#s,`#s,cs,b##s,us,e#%s,v'#m#*#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#*S2S;654S'S)s$A)s-$#'$&s$C#$s-'s,s&s+x$s,ss,r#s,q#s,ts,s##s-*s,v#%s-+'#m#*#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#*S2S;s#'s#&s#%S'S)s$@)s-5#'$&s$B#$s-8s-(&s,-$s-(s-'#s-&#s-)s-(##s-;s-+#%s-<'#m#*#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#*S2S;s#8s#7s#6S'S)s$?)s-F#'$&s$A#$s-Is-9&s,>$s-9s-8#s-7#s-:s-9##s-Ls-<#%s-M'#m#*#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#/S;2S;?S>*S2S=%$#S#S-s$@)s-Z#'$&s$B#$s-]s-M&s,R$s-Ms-L#s-K#s-Ns-M##s-`s-P#%s-a'#m#*#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#*S2S=876S#S-s$?)s-m#'$&s$A#$s-ps-`&s,e$s-`s-_#s-^#s-as-`##s-ss-c#%s-t'#m#*#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s$$s%cs#ss#_s#Ns#=s#,6#LnD#$#<FL#+$#=s&z$#;s&w&#>#:#5s&u&#>#:#5s&u&#>#:#5s&u&#>#:#5s&u'#?#@#;#As&m'#?#B#C#;s&m&s'l#nD#$#<s,zL#+$#=s&e$#;s&_&#>#:#5s'W&#>#:#5s'W&#>#:#5s'W&#>#:#5s'W'#?#@#;#As&X'#?#B#C#;s&X#s-rs-q##s.(s-t#%s.)&#m#)#,s&.s$?#El#5s&LC#'s'pnC#$##Fs(7#%#G##nC#$##Fs(4#%#G#s&LnD#$#<FK#+$#=s(:$#;$&#>#:#5#&#>#:#5#&#>#:#5#&#>#:#5#'#?#@#;#As'$'#?#B#C#;s'$&s(H##s-}s-|s'a#s.3s.##%s.4%#m#+#nR$H$#$Fs'.#%#s+@%#B#Ds((nC#$##FE#%#G##&s&v#nC#$#4s-1E#%#s&t#s,}nR$H$#$s-2s'2#%##%#B#Ds'`nC#$##s-3E#%#s&v###s.+s.*##s.=s.-#%s.>(#j#5C#)s.@s(*&s(,G#s.1s.0s(*#s.Cs.3#%s.D%#m#'#nR$H$#$FE#%#s-D%#B#Ds(8&s(*#nR$H$#$s-@E#%#s-0%#B#Ds'n#s.8s.7##s.Js.:#%s.K&#j#Ds.L#)s.Ms-L&s'0s-L#s.>s.=s-7#s.Ps.@#%s.Q%#m#'#)s.Ss(F&s&bs(F#s.Ds.Cs'{#s.Vs.F#%s.W%#m#'#j#Ds.Y#j#'H#V#JEj#Ds.\#j#'H#YSIH4.#El#Ds(Fs._#nR$H$#$Fs(G#%#s-^%#B#Ds(R&s(L#nR$H$#$s-Zs(I#%#s-J%#B#Ds(,#s.Rs.Q##s.ds.T#%s.e&#m#)#,s#*s#$#El#5s(.C#nR$H$#$Fs(7#%#s'k%#B#Ds([nC#$##Fs(0#%#G##&s)&#nC#$#4s-ds(2#%#s(;#s-TnR$H$#$s-es(;#%##%#B#Ds(7nC#$##s-fs(4#%#s(=###s.^s.]##s.ps.`#%s.q(#m#,#,s':s#@#El#5s)0C#4s.IJFS2MLEs(nS.'#'s(FnC#$##Fs'=#%#G##nD#$#<FJ#+$#=%$#;#&#>#:#5s'p&#>#:#5s'p&#>#:#5s'p&#>#:#5s'p'#?#@#;#As#M'#?#B#C#;s#M2S.?S%CS&S*s)=$#S'LKJ*S2S&s)>%$LKJnC#$##F$#%#G#s-}nR$H$#$F$#%##%#B#Ds(rnC#$##F&#%#G##nC#$#+Fs)>#%#*##&0#$s/(s.t0s-y$s.ts.s#s.r$s/*s.vs(Ts-{$s.vs.u#s.tnC#$##s.$s'L#%#s(W##nD#$#<s.%J#+$#=&$#;#&#>#:#5s'e&#>#:#5s'e&#>#:#5s'e&#>#:#5s'e'#?#@#;#As(e'#?#B#C#;s(e.S&S*s)J10LKJ(H8s..$s/0s.|#s.%$s.|s.{#s.znC#$#4s.*&#%###s-vnR$H$#$s.+3#%##%#B#Ds(YnC#$##s.,(#%#%##nC#$##s.-s)M#%#*##nC#$#4s..7#%#'#s-znR$H$#$s./7#%##%#B#Ds(]nC#$##s.09#%#)##nC#$##s.1s)Q#%#&###s/)s/(##s/;s/+#%s/<7#m#s#'#/s.n2s.o.S&S*s)\s##B$#JnC#$#4s.9##%#2#s.)nR$H$#$s.:B#%##%#B#Ds(hnC#$##s.;7#%#4##nC#$##s.<s)\#%#9##CS&S*s)as#(s#'S')(JnC#$#4s.>##%#7#s..nR$H$#$s.?s#'#%##%#B#Ds(mnC#$##s.@s#)#%#9##nC#$##s.As)a#%#'###s/9s/8##s/Ks/;#%s/Ls#'#m#2#ES&USJ#USNS&Ds(as(_s(M&$#USA&USMS&Ds.ks)bs(m%$#'s)JnC#$##Fs'v#%#G##@s.}S2s.ls.hs._POM'#nC#$##Fs(R#%#G##nD#$#<FJ#+$#=s#A$#;&&#>#:#5#&#>#:#5#&#>#:#5#&#>#:#5#'#?#@#;#As)['#?#B#C#;s)[]SA/S*s)ws#>s#=S'LKJ@0S2s)xs#?s#>LKJnC#$##F$#%#G#s.[nR$H$#$F$#%##%#B#Ds)PnC#$##F&#%#G##nC#$#+Fs)x#%#(##&s#J#%s/b#9m#1#68S*S.S%S#s#Ms)|S'&s#N#7S&S*S.S%S#s#Os/SS'#s/Vs/U##s/hs/X#%s/i&#m#)#DCs*'s)z#S)Ej#&s*)#j#<D#j#7I#j#%D#V#JEj#8I#j#9D#Ns*7#Ej#:S1#V#JEj#;D#j#:S1#1KJE<#nS7$D$#$S8##%$#%s/\#S91LKJ6s/[S.S%S#S-#S(S)&$#7S*S.S%S#S-%s/kS)#s/ns/m##s0$s/p#%s0%&#k#&*#k#'N#k#;D#j#*S1#1s/ZJE<#nS7$D$#$S8##%$#%s/W#S91s/ULK6s/TS,S+S&S*#ES%&$#7S5S,S+S&S*%s/yS%#s/|s/{##s02s/~#%s03&#j#+C#OS`USO#O$O#O#O#O#USO#VSa)#VSPE#:O#8#s.qnC#$##C##%#S4#s.nnC#$##F##%#G#s/@nC#$##Fs.p#%#G#s/A8s)6QnC#$##F##%#G#s/CBS::s(`#8#S$nC#$##F##%#G#s/GnD#$#<FL#+$#=*$#;)&#>#:#5'&#>#:#5'&#>#:#5'&#>#:#5''#?#@#;#A#'#?#B#C#;#\ES,s/`s/\s/SS%OMLnC#$##F##%#G#s/JnC#$#+Fs/a#%#%##&s###91s.|1s/)ML(H#s/P$s0Rs0B#s/G$s0Bs0A#s0@nC#$##s/L'#%###s/<nC#$##s/Ms/&#%#$#s/=1s.<PO(H#s/V$s0Xs0H#s/M$s0Hs0G#s0FnC#$##s/R8#%###s/B1s-FQP(H#s/[$s0]s0M#s/R$s0Ms0L#s0KnC#$##s/W9#%###s/GnD#$#<s/XL#+$#=.$#;-&#>#:#5(&#>#:#5(&#>#:#5(&#>#:#5('#?#@#;#A#'#?#B#C#;#.S5S,s/vs/rs/is/Ms/LL(Hs#7s/a$s0cs0S#s/X$s0Ss0R#s0QnC#$#4s/]&#%###s/MnC#$##s/^s/z#%#(##CS5S,s/|s/xs/oS%s/Ss/RLnC#$#4s/`##%#&#s/PnC#$##s/as/}#%#%###s0Ys0X##s0ks0[#%s0l@#j#5s0(#:Ps#28#s.qnC#$##C##%#S4#s.onC#$##F##%#G#s/onC#$##Fs.q#%#G#s/pBS?:s&f#8#S(nC#$##F##%#G#s/tnD#$#<FM#+$#=($#;'&#>#:#5s#0&#>#:#5s#0&#>#:#5s#0&#>#:#5s#0'#?#@#;#A#'#?#B#C#;#CS:S5s/Ds/Ms/CS.POMnC#$##F##%#G#s/wnC#$#+FE#%#%##&s#-#9/s.{1s/%OM(H#s/}$s1#s0o#s/t$s0os0n#s0mnC#$##s/y'#%###s/inC#$##s/zs/%#%#$#s/j1s-^S$Q(H#s0'$s1)s0u#s/z$s0us0t#s0snC#$##s0#4#%###s/onD#$#<s0$M#+$#=)$#;(&#>#:#5s#+&#>#:#5s#+&#>#:#5s#+&#>#:#5s#+'#?#@#;#A#'#?#B#C#;#.S:S5s/Us/^s/TPOMnC#$#4s0&##%#s#9#s/rnC#$##s0'E#%#%##nC#$#4s0(6#%#s#;#s/tnC#$##s0)E#%#$###s0}s0|##s13s1##%s147#j#5C#:Qs#V8#s.wnC#$##C##%#S4#JnC#$##F##%#G#s07nC#$##FJ#%#G#s08nC#$##FL#%#G#s09nC#$##FM#%#G#s0:nD#$#<FO#+$#=&$#;%&#>#:#5$&#>#:#5$&#>#:#5$&#>#:#5$'#?#@#;#A#'#?#B#C#;#&?#9*JnC#$##s08##%#s#E#s0(nC#$##s09J#%#s#F#s0)nC#$##s0:L#%#:#s0*1s(tS(S$(H#s0C$s1Es15#s0:$s15s14#s13nC#$##s0?M#%###s0/nD#$#<s0@O#+$#=*$#;)&#>#:#5(&#>#:#5(&#>#:#5(&#>#:#5('#?#@#;#A#'#?#B#C#;##s18s17##s1Js1:#%s1K/#j#5C#1s/QEMnC#$##C9#%#S4#S4nC#$##F##%#G#s0MnD#$#<FE#+$#=#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&&#9=S41s/9JO(H#s0S$s1Us1E#s0J$s1Es1D#s1CnC#$##s0O'#%###s0?1s.3LQ(H#s0X$s1Zs1J#s0O$s1Js1I#s1H1s)1MS$(H#s0\$s1^s1N#s0S$s1Ns1M#s1LnD#$#<s0XE#+$#=+$#;,&#>#:#5'&#>#:#5'&#>#:#5'&#>#:#5''#?#@#;#A#'#?#B#C#;##s1Ps1O##s1bs1R#%s1c4#j#AD#GK1s.A#QnC#$##CE#%#S4#S4nC#$##F##%#G#s0f&%#9ES4(H's0j$s1ls1\#s0a$s1\s1[#s1ZnC#$##s0f&#%###s0V#s1^s1]##s1ps1`#%s1q*#j#5C#9S4S4GJ1s.`#P(H#s0u$s1ws1g#s0l$s1gs1f#s1enC#$##s0q(#%###s0a#s1is1h##s1{s1k#)s1|#&*G%s1~#%m#%#nC#$##s0xs/T#%#*#s0h#s1ps1o##s2&s1r#)s2'#%s2()$m#$#,6)#El#5s#RC#1s/ns)uO&#s#<(H$s1-$s2/s1{#s1$$s1{s1z#s1ynC#$##s1)s#=#%###s0u#s1}s1|##s23s2##%s24)#m#,#j#II#U#Ej#II#1s/{s)xO(H#s19)s2;#&%G$s2=s2-%s12$s2-s2,#s2+#s2.s2-##s2@s20#%s2A'#m#)#j#;N#U#Ej#;N#>S-S'1#s)wS((H#s1G)s2I#&%G$s2Ks2;%s1@$s2;s2:#s29#s2<s2;##s2Ns2>#%s2O'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#14s)vS((H#s1X)s2Z#&%G$s2\s2L%s1Q$s2Ls2K#s2J#s2Ms2L##s2_s2O#%s2`'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#1s#%s)uS((H#s1i)s2k#&%G$s2ms2]%s1b$s2]s2\#s2[#s2^s2]##s2ps2`#%s2q'#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#1s#6s)tS((H#s1z)s2|#&%G$s2~s2n%s1s$s2ns2m#s2l#s2os2n##s3%s2q#%s3&'#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#>S%S#1#s)sS'(H#s20)s32#&%G$s34s3$%s2)$s3$s3##s2~#s3%s3$##s37s3'#%s38'#m#)#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#16s)rS'(H#s2C)s3E#&%G$s3Gs37%s2<$s37s36#s35#s38s37##s3Js3:#%s3K'#m#)#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s$Ps#|s#os#]s#Ls#;s#*6#MnC#$##Cs%F#%#S4#S4nC#$##F##%#G#s2VnD#$#<FM#+$#=#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&s%h#9s%JS4nC#$##s2T##%#s%:#s2DnD#$#<s2UM#+$#=#$#;s%;&#>#:#5s%]&#>#:#5s%]&#>#:#5s%]&#>#:#5s%]'#?#@#;#As%5'#?#B#C#;s%5#s3Ms3L##s3_s3O#%s3`(#m#-#nC#$##Cs%-#%#S4#S6nC#$##F##%#G#s2anD#$#<FE#+$#=#$#;s2b&#>#:#5s2b&#>#:#5s2b&#>#:#5s2b&#>#:#5s2b'#?#@#;#As2b'#?#B#C#;s2b&s$v#9s%1S6nC#$##s2_##%#s$o#s2OnD#$#<s2`E#+$#=#$#;s2P&#>#:#5s2P&#>#:#5s2P&#>#:#5s2P&#>#:#5s2P'#?#@#;#As2P'#?#B#C#;s2P#s3Xs3W##s3js3Z#%s3k(#j#AD#nC#$##CE#%#S4#S6nC#$##F##%#G#s2l&s$g#9ES6nC#$##s2i##%#s$b#s2Y#s3as3`##s3ss3c#%s3t'#j#5C#9S4S6nC#$##s2o##%#s$]#s2_#s3gs3f##s3ys3i#)s3z#%s3{s$\$m#$#nC#$##s2us1I#%#s$c#s2e#s3ms3l##s4#s3o#)s4$#&s$js3#%s4&#%m#%#,1*#El#5s%PC#&s$\s#%nC#$##s3#s###%#s$Y#s2o#s3ws3v##s4-s3y#%s4.&#m#(#j#II#U#Ej#II#&s$Xs31%s44#s(Bm#s(F#j#;N#U#Ej#;N#&s$Ps37%s4:#s(Hm#s(L#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#&s$Is3A%s4D#s(Rm#s(V#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#&s$Bs3K%s4N#s(\m#s(`#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#&s$;s3U%s4X#s(fm#s(j#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#&s$3s3_%s4b#s(pm#s(t#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#&s$,s3k%s4n#s(|m#s)$#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s#ks#Is#Cs#9s#/s#%;/#MnC#$##Cs&i#%#S4#S6nC#$##F##%#G#s3ynD#$#<FM#+$#=#$#;s3z&#>#:#5s3z&#>#:#5s3z&#>#:#5s3z&#>#:#5s3z'#?#@#;#As3z'#?#B#C#;s3z&s'/#9s&mS6nC#$##s3w##%#s&]#s3gnD#$#<s3xM#+$#=#$#;s3h&#>#:#5s3h&#>#:#5s3h&#>#:#5s3h&#>#:#5s3h'#?#@#;#As3h'#?#B#C#;s3h#s4ps4o##s5&s4r#%s5'(#m#-#,s&;s$&#El#5s47C#&s'\s'?#s4ws4vs'*#s5-s4y#%s5.%#m#'#CS5S,s4Es4As48S%OML&s&ns2;nC#$#4s4*E#%#s&l#s3v#s4~s4}##s54s5$#%s55&#j#5C#)s57s'D&s'FG#s5(s5's'D#s5:s5*#%s5;%#m#'#&s'Ks4;%s5>#s)Lm#s)P#,,&#El#53C#nC#$##F4#%#G#s4@&s't#nC#$#4s4<6#%#s'>#s4,#s54s53##s5Fs56#%s5G&#m#)#,s&r<#El#5s4sC#1s1%KJ:Ms'l8#s4^nC#$##C##%#S4#s4[nC#$##F##%#G#s4MnC#$##Fs4]#%#G#s4NnD#$#<FK#+$#=$$#;#&#>#:#5s'=&#>#:#5s'=&#>#:#5s'=&#>#:#5s'='#?#@#;#As'j'#?#B#C#;s'jCS,S+s5#s1(s0{S#MLKnC#$##F##%#G#s4QnC#$#+Fs4}#%#%##&,#9+s4cnC#$##s4O##%#s'Q#s4?nC#$##s4Ps4e#%#s'R#s4@nD#$#<s4QK#+$#=$$#;#&#>#:#5s'5&#>#:#5s'5&#>#:#5s'5&#>#:#5s'5'#?#@#;#As']'#?#B#C#;s'].S,S+s5+s10s1'MLK(H2s4Z$s5\s5L#s4Q$s5Ls5K#s5JnC#$#4s4V&#%###s4FnC#$##s4Ws5,#%#(##nC#$#4s4X0#%#%#s4HnC#$##s4Ys5.#%#$###s5Qs5P##s5cs5S#%s5d1#m#=#.S,S+s57s1<s13s0ls0kKnC#$#4s4_##%#,#s4OnC#$##s4`s55#%#1##CS,S+s5:s1?s16S#s0os0nKnC#$#4s4b##%#/#s4RnC#$##s4cs58#%#%###s5[s5Z##s5ms5]#%s5n;#m#,#Ds5+s5*s'a#s0es0dVSPESB:M#8#s5(nC#$##C##%#S4#s5%nC#$##F##%#G#s4snD#$#<FK#+$#=#$#;s#(&#>#:#5s'b&#>#:#5s'b&#>#:#5s'b&#>#:#5s'b'#?#@#;#As(3'#?#B#C#;s(3]SAs0mS+s5Hs1Ms1DS#MLKnC#$##F##%#G#s4vnC#$#+Fs5F#%#%##&s#1#%s5{#0m#.#6s0sS+S&S*S.s#4s5JS#&s#5#7S,S+S&S*S.s#6s5lS##s5os5n##s6%s5q#%s6&&#m#)#DCs5Qs(R#S-Ej#&s([#j#LN#j#<D#j#7I#j#%D#V#JEj#8I#j#9D#Ns(f#Ej#:S1#W#KJEj#'N#j#;D#j#:S1#-JE<#/S'=E#%CP#nS7$D$#$S8&#%$#%##S9k#0Ds5Yk#1I#k#2D#k#3SF#USQS#-LK2S#K#LAM#-M$(H#s5FnC#$##s6H%#%###s5GBS-:)#LM#A#L-$L(H#s5MnC#$##s6O%#%###s5N0H*#'#MMOA#s(t2S%?S#GSbG'[KS.s6<&%$O#nC#$##F##%#G#s5WnC#$##F)#%###s5XnI#$#IFE#&#,$#M#$#M#MLMA#s(~/S#?S-G&QS%%@$-M#nC#$##F##%#G#s5`nC#$##F(#%###s5aMOPA#s)*G$RS*s1's*Js*I3P#nC#$##F##%#G#s5fnC#$##F&#%###s5gMPQA#s)0G$SS&s0zs0es0d9Q#nC#$##F##%#G#s5lnC#$##F&#%###s5mnD#$#GFs1B#+$#I7$#;/&#>#:#5)&#>#:#5)&#>#:#5)&#>#:#5)'#?#N#;#A#'#?#B#C#;#&s#1#$s6rs6bs#$s5g$s6bs6a#s6`>@O/#2$.S*S.s6[s#%s#$$#B-OM(H#s5x$s6zs6j#s5o$s6js6i#s6hnC#$#4s5t'#%###s5dnC#$##s5us#,#%###s5enI#$#Is5vE#&#-$#M#$#M#>s#+M/#2$.S.S%s#&s#As#%$#s#$-ML(H#s6'$s7)s6u#s5z$s6us6t#s6snC#$#4s6#'#%###s5onC#$##s6$s#-#%###s5p>s#5P/#2$.S&S*s1Ls*os*n$#s#(-PO(H#s61$s73s7##s6($s7#s6~#s6}nC#$#4s6-'#%###s5ynC#$##s6.s#/#%###s5z>s#?Q/#2$.S+S&s1Gs12s11$#s#,-QP(H#s6;$s7=s7-#s62$s7-s7,#s7+nC#$#4s67'#%###s6'nC#$##s68s#3#%###s6(nD#$#$s69s1o#+$#IA$#;7&#>#:#5-&#>#:#5-&#>#:#5-&#>#:#5-'#?#N#;#A#'#?#B#C#;##s71s70##s7Cs73#%s7Ds#1#j#5s#c#2S'K#JAK#Ks#SM-O#(H#s6JnC#$##s7LJ#%###s6KBS#:s#X#LO#A#M-$M(H#s6QnC#$##s7S%#%###s6R0H*#'#.S&S*s1rs+9s+8s#^Ps#NnC#$##F##%#G#s6UnC#$##Fs#Q#%###s6VnI#$#IFE#&#&$#M#$#M#.S*S.s7>s#ds#cs#bOs#anC#$##F##%#G#s6YnC#$##Fs#g#%###s6Z.S+S&s1js1Us1Ts#eQs#OnC#$##F##%#G#s6\nC#$##Fs#R#%###s6]MQS$A#s*&G$.S,S+s74s39s30s#kS$#nC#$##F##%#G#s6bnC#$##F&#%###s6cnD#$#GFs#f#+$#I/$#;,&#>#:#5)&#>#:#5)&#>#:#5)&#>#:#5)'#?#N#;#A#'#?#B#C#;#&s#B#$s7hs7X6s6]$s7Xs7W#s7VnC#$#4s6b6#%#s#8#s6RnC#$##s6cs#d#%###s6SnI#$#Is6dE#&#%$#M#$#M#nC#$#4s6e5#%#s#P#s6UnC#$##s6fs#y#%###s6VnC#$#4s6g4#%#s#3#s6WnC#$##s6hs#c#%###s6X-S$Q(H#s6q$s7ss7c#s6h$s7cs7b#s7anC#$#4s6m4#%###s6]nC#$##s6n7#%###s6^nD#$#$s6os#w#+$#I-$#;+&#>#:#5)&#>#:#5)&#>#:#5)&#>#:#5)'#?#N#;#A#'#?#B#C#;##s7gs7f##s7ys7i#%s7z5#j#5C#2S-BS':$#LL#A#KKs+dO-P#(H#s7&BS%:s+h#LP#-#O(H#s7+nC#$##s8-J#%###s7,0H)#'#nI#$#IFE#&##$#Ms#/$#Ms#/MS$S(A#s*SG$.S5S,s7Is7Es7<s$<S(#nC#$##F##%#G#s73nC#$##F&#%###s74nD#$#GFs7w#+$#I)$#;s#=&#>#:#5s#0&#>#:#5s#0&#>#:#5s#0&#>#:#5s#0'#?#N#;#A#'#?#B#C#;#&s#z#$s89s8)-s7.$s8)s8(#s8'nI#$#Is73E#&##$#Ms#)$#Ms#)-S(S$(H#s7<$s8>s8.#s73$s8.s8-#s8,nC#$#4s78.#%###s7(nC#$##s791#%###s7)nD#$#$s7:s8&#+$#I)$#;s#5&#>#:#5s#*&#>#:#5s#*&#>#:#5s#*&#>#:#5s#*'#?#N#;#A#'#?#B#C#;##s82s81##s8Ds84#%s8E/#j#5C#Ks2?P-Q#(H#s7HLQs0k-#P(H#s7K0H&#'#nC#$##FK#%#s#I#s7MnI#$#IFE#&#$$#M#$#M#nC#$##FJ#%#s#Q#s7OnC#$##FL#%#?#s7PMS(S)G#.S:S5s6}s7*s6|s$]S)#nC#$##F##%#G#s7TnC#$##FM#%###s7UnD#$#GFs2t#+$#I*$#;)&#>#:#5(&#>#:#5(&#>#:#5(&#>#:#5('#?#N#;#A#'#?#B#C#;#&s$*#$s8Zs8J/s7O$s8Js8I#s8HnC#$##s7TK#%#s#E#s7DnI#$#Is7UE#&#$$#M#$#M#nC#$##s7VJ#%#s#M#s7FnC#$##s7WL#%#A#s7G-S)S((H#s7`$s8bs8R#s7W$s8Rs8Q#s8PnC#$#4s7\1#%###s7LnC#$##s7]M#%###s7MnD#$#$s7^s3&#+$#I+$#;*&#>#:#5)&#>#:#5)&#>#:#5)&#>#:#5)'#?#N#;#A#'#?#B#C#;##s8Vs8U##s8hs8X#%s8i2#j#5C#Ks4AQ-S$#(H#s7lLS$s4A-#Q(H#s7o0H&#'#nC#$##FK#%#G#s7qnI#$#IFE#&#$$#M#$#M#nD#$#GFs3&#+$#I#$#;s*=&#>#:#5s*<&#>#:#5s*<&#>#:#5s*<&#>#:#5s*<'#?#N#;#As*;'#?#B#C#;s*;&s$=#$s8ws8g(s7l$s8gs8f#s8enC#$#4s7qK#%#s#<#s7anI#$#Is7rE#&#$$#M#$#M#nC#$#4s7sJ#%#s#e#s7cnC#$#4s7tL#%#;#s7d-S'S)(H#s7}$s9#s8o#s7t$s8os8n#s8mnC#$#4s7yM#%###s7inD#$#$s7zs33#+$#I*$#;)&#>#:#5(&#>#:#5(&#>#:#5(&#>#:#5('#?#N#;#A#'#?#B#C#;##s8rs8q##s9(s8t#%s9)1#j#5C#Ks8<S$-S(#(H#s8,LS(s8<-#S$(H#s8/0H&#'#nI#$#IFE#&##$#MG$#MGnD#$#GFE#+$#I#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s#~#$s96s9&'s8+$s9&s9%#s9$nI#$#Is80E#&##$#Ms#3$#Ms#3-S-S'(H#s89$s9;s9+#s80$s9+s9*#s9)nD#$#$s85E#+$#I'$#;s#\&#>#:#5;&#>#:#5;&#>#:#5;&#>#:#5;'#?#N#;#A#'#?#B#C#;##s9-s9,##s9?s9/#%s9@-#j#AD#Ks7sS(-S)#(H#s8CLS)s7s-#S((H#s8F0H&#'#nI#$#IFE#&##$#MG$#MG&s#I#$s9Ls9<&s8A$s9<s9;#s9:nI#$#Is8FE#&##$#Ms#,$#Ms#,#s9>s9=##s9Ps9@#%s9Q(#j#II#)s9Ss#$&s#vs#$#s9Ds9C@#s9Vs9F#%s9W%#m#'#)s9Ys#9&s#;G#s9Js9Is#9#s9\s9L#%s9]%#m#'#j#MS@#U#Ej#MS@#H2,##E&s$)s#2#s9Ss9Rs#.#s9es9U#%s9f%#m#'#j#II#U#Ej#II#)s9ks$0&s$2G#s9\s9[s$0#s9ns9^#%s9o%#m#'#j#;N#U#Ej#;N#-S#S-(H#s8t)s9v#&%G$s9xs9h%s8m$s9hs9g#s9f#s9is9h##s9{s9k#%s9|'#m#)#j#OD#j#PD#j#>S/#W#KJEj#5D#j#:D#j#>S/#j#>S0(W#KJEj#5D#j#:D#j#>S0#-S.S%(H#s9.)s:0#&%G$s:2s9~%s9'$s9~s9}#s9|#s:#s9~##s:5s:%#%s:6'#m#)#j#AD#j#;N#j#NN#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#j#;N,j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s#gs#>s#5s#$s#$??,#El#As4gD#nI#$#IFE#&#s$\$#MG$#MGnD#$#GFs4i#+$#I#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s%{#nI#$#Is9GE#&#s$R$#Ms%9$#Ms%9nD#$#$s9Hs4l#+$#I#$#;s%p&#>#:#5s$o&#>#:#5s$o&#>#:#5s$o&#>#:#5s$o'#?#N#;#As$K'#?#B#C#;s$K#s:@s:?##s:Rs:B#%s:S'#m#+#nI#$#IFE#&#s$%$#Ms9S$#Ms9SnD#$#GFE#+$#I#$#;s9T&#>#:#5s9T&#>#:#5s9T&#>#:#5s9T&#>#:#5s9T'#?#N#;#As9T'#?#B#C#;s9T&s%D#nI#$#Is9PE#&#s$#$#Ms9@$#Ms9@nD#$#$s9QE#+$#I#$#;s9A&#>#:#5s9A&#>#:#5s9A&#>#:#5s9A&#>#:#5s9A'#?#N#;#As9A'#?#B#C#;s9A#s:Is:H##s:[s:K#%s:\'#j#AD#nI#$#IFE#&#s#s$#Ms9\$#Ms9\&s$]#nI#$#Is9XE#&#s#q$#Ms9H$#Ms9H#s:Ps:O##s:bs:R#%s:c&#j#II#&s$Fs9c%s:f#s.tm#s.x#j#MS@#U#Ej#MS@#H)s#q##E&s%29#s:\s:[7#s:ns:^#%s:o%#m#'#j#II#U#Ej#II#&s%:s9r%s:u#s/'m#s/+#j#;N#U#Ej#;N#&s#ds9x%s:{#s/-m#s/1#j#OD#j#PD#j#>S/#W#KJEj#5D#j#:D#j#>S/#j#>S0(W#KJEj#5D#j#:D#j#>S0#&s#]s:+%s;.#s/<m#s/@#j#AD#j#;N#j#NN#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#j#;N,j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s#Cs#-s#'==88,#El#As5_D#nI#$#IFE#&#s%T$#Ms:B$#Ms:BnD#$#GFs5a#+$#I#$#;s:C&#>#:#5s:C&#>#:#5s:C&#>#:#5s:C&#>#:#5s:C'#?#N#;#As:C'#?#B#C#;s:C&s&s#nI#$#Is:?E#&#s%J$#Ms:/$#Ms:/nD#$#$s:@s5d#+$#I#$#;s:0&#>#:#5s:0&#>#:#5s:0&#>#:#5s:0&#>#:#5s:0'#?#N#;#As:0'#?#B#C#;s:0#s;8s;7##s;Js;:#%s;K'#m#+#,s%%s#W#El#5s&RC#0Hs&*s&%'#nI#$#IFE#&##$#Ms&Q$#Ms&QnD#$#GFs;6#+$#I#$#;s&Y&#>#:#5s&L&#>#:#5s&L&#>#:#5s&L&#>#:#5s&L'#?#N#;#As%{'#?#B#C#;s%{&s'9#$s;Ts;D's:I$s;Ds;C#s;BnI#$#Is:NE#&##$#Ms&E$#Ms&EnD#$#$s:Os;;#+$#I#$#;s&K&#>#:#5s&@&#>#:#5s&@&#>#:#5s&@&#>#:#5s&@'#?#N#;#As%u'#?#B#C#;s%u#s;Gs;F##s;Ys;I#%s;Z)#m#/#nI#$#IFE#&#s%H$#Ms:Z$#Ms:ZnD#$#GFE#+$#I#$#;s:[&#>#:#5s:[&#>#:#5s:[&#>#:#5s:[&#>#:#5s:['#?#N#;#As:['#?#B#C#;s:[&s'%#nI#$#Is:WE#&#s%E$#Ms:G$#Ms:GnD#$#$s:XE#+$#I#$#;s:H&#>#:#5s:H&#>#:#5s:H&#>#:#5s:H&#>#:#5s:H'#?#N#;#As:H'#?#B#C#;s:H#s;Ps;O##s;bs;R#%s;c'#j#AD#j#IIs#T)s;fs%S&s&Ts%S#s;Ws;Vs%N#s;is;Y#%s;j%#m#'#&s%js:j%s;m#s/{m#s0##j#MS@#U#Ej#MS@#H/)##E&s&`9#s;cs;b7#s;us;e#%s;v%#m#'#j#II#U#Ej#II#&s&hs:y%s;|#s0.m#s02#j#;N#U#Ej#;N#&s%Js;#%s<&#s04m#s08#j#OD#j#PD#j#>S/#W#KJEj#5D#j#:D#j#>S/#j#>S0(W#KJEj#5D#j#:D#j#>S0#-S%S#&#s;3%s<6#s0Dm#s0H#j#AD#j#;N#j#NN#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#j#;N,j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s#Ds#.s#(>>99,#El#As</D#nI#$#IFE#&#s#Z$#Ms;J$#Ms;JnD#$#GFs<1#+$#I#$#;s;K&#>#:#5s;K&#>#:#5s;K&#>#:#5s;K&#>#:#5s;K'#?#N#;#As;K'#?#B#C#;s;K&s(4#nI#$#Is;GE#&#s#X$#Ms;7$#Ms;7nD#$#$s;Hs<4#+$#I#$#;s;8&#>#:#5s;8&#>#:#5s;8&#>#:#5s;8&#>#:#5s;8'#?#N#;#As;8'#?#B#C#;s;8#s<@s<?##s<Rs<B#%s<S'#m#+#,s&Is#X#El#5s(WC#0Hs'js'c'#nI#$#IFE#&##$#Ms'_$#Ms'_nD#$#GFs(Z#+$#I#$#;s'\&#>#:#5s'Y&#>#:#5s'Y&#>#:#5s'Y&#>#:#5s'Y'#?#N#;#As'S'#?#B#C#;s'S&s(6#$s<\s<L's;Q$s<Ls<K#s<JnI#$#Is;VE#&##$#Ms'Q$#Ms'QnD#$#$s;Ws(_#+$#I#$#;s'O&#>#:#5s'M&#>#:#5s'M&#>#:#5s'M&#>#:#5s'M'#?#N#;#As'G'#?#B#C#;s'G#s<Os<N##s<as<Q#%s<b)#m#/#0Hs&ys;c'#nI#$#IFE#&##$#Ms&u$#Ms&unD#$#GFs7'#+$#I#$#;s&t&#>#:#5s&s&#>#:#5s&s&#>#:#5s&s&#>#:#5s&s'#?#N#;#As&n'#?#B#C#;s&n&s(9#$s<is<Y's;^$s<Ys<X#s<WnI#$#Is;cE#&##$#Ms&m$#Ms&mnD#$#$s;ds7,#+$#I#$#;s&l&#>#:#5s&k&#>#:#5s&k&#>#:#5s&k&#>#:#5s&k'#?#N#;#As&e'#?#B#C#;s&e#s<\s<[##s<ns<^#%s<o)#j#5C#0Hs&bs;p'#nI#$#IFE#&##$#Ms&^$#Ms&^nD#$#GFs7%#+$#I#$#;s.<&#>#:#5s.;&#>#:#5s.;&#>#:#5s.;&#>#:#5s.;'#?#N#;#As.:'#?#B#C#;s.:&s(<#$s<vs<f's;k$s<fs<e#s<dnI#$#Is;pE#&##$#Ms&]$#Ms&]nD#$#$s;qs7*#+$#I#$#;s&\&#>#:#5s&[&#>#:#5s&[&#>#:#5s&[&#>#:#5s&['#?#N#;#As&V'#?#B#C#;s&V#s<is<h##s<{s<k#%s<|)#j#5C#0Hs&Ss;}'#nI#$#IFE#&##$#MG$#MGnD#$#GFE#+$#I#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s'o#$s='s<s's;x$s<ss<r#s<qnI#$#Is;}E#&##$#Ms'$$#Ms'$nD#$#$s;~E#+$#I#$#;s'I&#>#:#5s&d&#>#:#5s&d&#>#:#5s&d&#>#:#5s&d'#?#N#;#As&L'#?#B#C#;s&L#s<vs<u##s=,s<x#%s=-)#j#AD#0Hs&Is<.'#nI#$#IFE#&##$#MG$#MG&s'0#$s=3s=#&s<($s=#s<~#s<}nI#$#Is<-E#&##$#Ms&o$#Ms&o#s=%s=$##s=7s='#%s=8(#j#II#)s=::&s']:#s=+s=*6#s==s=-#%s=>%#m#'#H)#s&=s&=E&s'c?#s=1s=0;#s=Cs=3#%s=D%#m#'#j#II#U#Ej#II#;=#s&4s&#s&#s%zs%zs%gs%^El#As7fD#nI#$#IFE#&#s#D$#MG$#MGnD#$#GFs7h#+$#I#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s(z#nI#$#Is<FE#&#s#B$#Ms(8$#Ms(8nD#$#$s<Gs7k#+$#I#$#;s(o&#>#:#5s'n&#>#:#5s'n&#>#:#5s'n&#>#:#5s'n'#?#N#;#As'J'#?#B#C#;s'J#s=?s=>##s=Qs=A#%s=R'#m#+#nI#$#IFE#&#s#3$#Ms<R$#Ms<RnD#$#GFE#+$#I#$#;s<S&#>#:#5s<S&#>#:#5s<S&#>#:#5s<S&#>#:#5s<S'#?#N#;#As<S'#?#B#C#;s<S&s(C#nI#$#Is<OE#&#s#1$#Ms<?$#Ms<?nD#$#$s<PE#+$#I#$#;s<@&#>#:#5s<@&#>#:#5s<@&#>#:#5s<@&#>#:#5s<@'#?#N#;#As<@'#?#B#C#;s<@#s=Hs=G##s=Zs=J#%s=['#j#AD#nI#$#IFE#&#s#/$#Ms<[$#Ms<[&s'\#nI#$#Is<WE#&#s#-$#Ms<G$#Ms<G#s=Os=N##s=as=Q#%s=b&#j#II#H#s#'s%Xs%XE&s(+3#s=Us=T1#s=gs=W#%s=h%#m#'#j#II#U#Ej#II#;3#s%Rs%Hs%Hs%Cs%Cs%7s%.El#As8.D#nI#$#IFE#&#s#h$#Ms<m$#Ms<mnD#$#GFs80#+$#I#$#;s<n&#>#:#5s<n&#>#:#5s<n&#>#:#5s<n&#>#:#5s<n'#?#N#;#As<n'#?#B#C#;s<n&s)B#nI#$#Is<jE#&#s#f$#Ms<Z$#Ms<ZnD#$#$s<ks83#+$#I#$#;s<[&#>#:#5s<[&#>#:#5s<[&#>#:#5s<[&#>#:#5s<['#?#N#;#As<['#?#B#C#;s<[#s=cs=b##s=us=e#%s=v'#m#+#,s#Ys#'#El#5s(}C#0Hs(Us<y'#nI#$#IFE#&##$#Ms(|$#Ms(|nD#$#GFs=a#+$#I#$#;s)(&#>#:#5s(w&#>#:#5s(w&#>#:#5s(w&#>#:#5s(w'#?#N#;#As(J'#?#B#C#;s(J&s)d#$s>#s=o's<t$s=os=n#s=mnI#$#Is<yE#&##$#Ms(p$#Ms(pnD#$#$s<zs=f#+$#I#$#;s(v&#>#:#5s(k&#>#:#5s(k&#>#:#5s(k&#>#:#5s(k'#?#N#;#As(D'#?#B#C#;s(D#s=rs=q##s>(s=t#%s>))#m#/#nI#$#IFE#&#s#s$#Ms=)$#Ms=)nD#$#GFE#+$#I#$#;s=*&#>#:#5s=*&#>#:#5s=*&#>#:#5s=*&#>#:#5s=*'#?#N#;#As=*'#?#B#C#;s=*&s)P#nI#$#Is=&E#&#s#q$#Ms<r$#Ms<rnD#$#$s='E#+$#I#$#;s<s&#>#:#5s<s&#>#:#5s<s&#>#:#5s<s&#>#:#5s<s'#?#N#;#As<s'#?#B#C#;s<s#s={s=z##s>1s=}#%s>2'#j#AD#j#IIs#*)s>5s#~&s)#s#~#s>&s>%s#z#s>8s>(#%s>9%#m#'#H)#s%(s%(E&s))3#s>,s>+1#s>>s>.#%s>?%#m#'#j#II#U#Ej#II#;3#s$~s$ts$ts$os$os$bs$YEl#As>)D#nI#$#IFE#&#s#)$#Ms=D$#Ms=DnD#$#GFs>+#+$#I#$#;s=E&#>#:#5s=E&#>#:#5s=E&#>#:#5s=E&#>#:#5s=E'#?#N#;#As=E'#?#B#C#;s=E&s*.#nI#$#Is=AE#&#s#'$#Ms=1$#Ms=1nD#$#$s=Bs>.#+$#I#$#;s=2&#>#:#5s=2&#>#:#5s=2&#>#:#5s=2&#>#:#5s=2'#?#N#;#As=2'#?#B#C#;s=2#s>:s>9##s>Ls><#%s>M'#m#+#,s$=s#'#El#5s*QC#0Hs)ds=P'#nI#$#IFE#&##$#Ms)Y$#Ms)YnD#$#GFs*T#+$#I#$#;s)V&#>#:#5s)S&#>#:#5s)S&#>#:#5s)S&#>#:#5s)S'#?#N#;#As)M'#?#B#C#;s)M&s*0#$s>Vs>F's=K$s>Fs>E#s>DnI#$#Is=PE#&##$#Ms)K$#Ms)KnD#$#$s=Qs*Y#+$#I#$#;s)I&#>#:#5s)G&#>#:#5s)G&#>#:#5s)G&#>#:#5s)G'#?#N#;#As)A'#?#B#C#;s)A#s>Is>H##s>[s>K#%s>\)#m#/#,s(vs$Y#El#5s)=C#0Hs*ws*o'#nI#$#IFE#&##$#Ms)d$#Ms)d.S.S%s*cs*~s*bs*kMs*anC#$##F##%#G#s=bnC#$##Fs*f#%###s=cnD#$#GFs98#+$#I&$#;#&#>#:#5s)l&#>#:#5s)l&#>#:#5s)l&#>#:#5s)l'#?#N#;#As)e'#?#B#C#;s)e&s+'#$s>hs>X*s=]$s>Xs>W#s>VnI#$#Is=bE#&##$#Ms)Z$#Ms)ZnC#$#4s=c*#%#s*C#s=SnC#$##s=ds*m#%###s=TnD#$#$s=es9?#+$#I%$#;#&#>#:#5s)`&#>#:#5s)`&#>#:#5s)`&#>#:#5s)`'#?#N#;#As)['#?#B#C#;s)[#s>]s>\##s>os>_#%s>p+#m#4#0Hs=qs)G'#nI#$#IFE#&##$#Ms)s$#Ms)snD#$#GFs>Y#+$#I#$#;s){&#>#:#5s)n&#>#:#5s)n&#>#:#5s)n&#>#:#5s)n'#?#N#;#As)A'#?#B#C#;s)A&s*\#$s>ws>g's=l$s>gs>f#s>enI#$#Is=qE#&##$#Ms)g$#Ms)gnD#$#$s=rs>^#+$#I#$#;s)m&#>#:#5s)b&#>#:#5s)b&#>#:#5s)b&#>#:#5s)b'#?#N#;#As);'#?#B#C#;s);#s>js>i##s>|s>l#%s>})#j#5C#0Hs=~s)5'#nI#$#IFE#&##$#Ms)4$#Ms)4nD#$#GFs9B#+$#I#$#;s)3&#>#:#5s)2&#>#:#5s)2&#>#:#5s)2&#>#:#5s)2'#?#N#;#As)-'#?#B#C#;s)-&s*T#$s?(s>t's=y$s>ts>s#s>rnI#$#Is=~E#&##$#Ms),$#Ms),nD#$#$s>#s9G#+$#I#$#;s)+&#>#:#5s)*&#>#:#5s)*&#>#:#5s)*&#>#:#5s)*'#?#N#;#As)$'#?#B#C#;s)$#s>ws>v##s?-s>y#%s?.)#j#5C#0Hs>/s(z'#nI#$#IFE#&##$#Ms(y$#Ms(ynD#$#GFs9@#+$#I#$#;s0W&#>#:#5s0V&#>#:#5s0V&#>#:#5s0V&#>#:#5s0V'#?#N#;#As0U'#?#B#C#;s0U&s*W#$s?5s?%'s>*$s?%s?$#s?#nI#$#Is>/E#&##$#Ms(x$#Ms(xnD#$#$s>0s9E#+$#I#$#;s(w&#>#:#5s(v&#>#:#5s(v&#>#:#5s(v&#>#:#5s(v'#?#N#;#As(q'#?#B#C#;s(q#s?(s?'##s?:s?*#%s?;)#j#5C#0Hs><s(k'#nI#$#IFE#&##$#MG$#MGnD#$#GFE#+$#I#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s*.#$s?Bs?2's>7$s?2s?1#s?0nI#$#Is><E#&##$#Ms)?$#Ms)?nD#$#$s>=E#+$#I#$#;s)d&#>#:#5s)#&#>#:#5s)#&#>#:#5s)#&#>#:#5s)#'#?#N#;#As(g'#?#B#C#;s(g#s?5s?4##s?Gs?7#%s?H)#j#AD#0Hs>Is(a'#nI#$#IFE#&##$#MG$#MG&s)K#$s?Ns?>&s>C$s?>s?=#s?<nI#$#Is>HE#&##$#Ms).$#Ms).#s?@s??##s?Rs?B#%s?S(#j#II#)s?U:&s)x:#s?Fs?E6#s?Xs?H#%s?Y%#m#'#H)#s(Xs(XE&s)~?#s?Ls?K;#s?^s?N#%s?_%#m#'#j#II#U#Ej#II#;=#s(Os(>s(>s(9s(9s(&s'yEl#As:%D#nI#$#IFE#&#s#D$#MG$#MGnD#$#GFs:'#+$#I#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s+9#nI#$#Is>aE#&#s#B$#Ms*S$#Ms*SnD#$#$s>bs:*#+$#I#$#;s+.&#>#:#5s*-&#>#:#5s*-&#>#:#5s*-&#>#:#5s*-'#?#N#;#As)e'#?#B#C#;s)e#s?Zs?Y##s?ls?\#%s?m'#m#+#nI#$#IFE#&#s#3$#Ms>m$#Ms>mnD#$#GFE#+$#I#$#;s>n&#>#:#5s>n&#>#:#5s>n&#>#:#5s>n&#>#:#5s>n'#?#N#;#As>n'#?#B#C#;s>n&s*^#nI#$#Is>jE#&#s#1$#Ms>Z$#Ms>ZnD#$#$s>kE#+$#I#$#;s>[&#>#:#5s>[&#>#:#5s>[&#>#:#5s>[&#>#:#5s>['#?#N#;#As>['#?#B#C#;s>[#s?cs?b##s?us?e#%s?v'#j#AD#nI#$#IFE#&#s#/$#Ms>v$#Ms>v&s)w#nI#$#Is>rE#&#s#-$#Ms>b$#Ms>b#s?js?i##s?|s?l#%s?}&#j#II#H#s#'s'ss'sE&s*F3#s?ps?o1#s@&s?r#%s@'%#m#'#j#II#U#Ej#II#;3#s'ms'cs'cs'^s'^s'Rs'IEl#As:ID#nI#$#IFE#&#s#h$#Ms?,$#Ms?,nD#$#GFs:K#+$#I#$#;s?-&#>#:#5s?-&#>#:#5s?-&#>#:#5s?-&#>#:#5s?-'#?#N#;#As?-'#?#B#C#;s?-&s+]#nI#$#Is?)E#&#s#f$#Ms>u$#Ms>unD#$#$s?*s:N#+$#I#$#;s>v&#>#:#5s>v&#>#:#5s>v&#>#:#5s>v&#>#:#5s>v'#?#N#;#As>v'#?#B#C#;s>v#s?~s?}##s@4s@$#%s@5'#m#+#,s#Ys#'#El#5s+<C#0Hs?8s*k'#nI#$#IFE#&##$#Ms+;$#Ms+;nD#$#GFs?|#+$#I#$#;s+C&#>#:#5s+6&#>#:#5s+6&#>#:#5s+6&#>#:#5s+6'#?#N#;#As*e'#?#B#C#;s*e&s,##$s@>s@.'s?3$s@.s@-#s@,nI#$#Is?8E#&##$#Ms+/$#Ms+/nD#$#$s?9s@%#+$#I#$#;s+5&#>#:#5s+*&#>#:#5s+*&#>#:#5s+*&#>#:#5s+*'#?#N#;#As*_'#?#B#C#;s*_#s@1s@0##s@Cs@3#%s@D)#m#/#nI#$#IFE#&#s#s$#Ms?D$#Ms?DnD#$#GFE#+$#I#$#;s?E&#>#:#5s?E&#>#:#5s?E&#>#:#5s?E&#>#:#5s?E'#?#N#;#As?E'#?#B#C#;s?E&s+k#nI#$#Is?AE#&#s#q$#Ms?1$#Ms?1nD#$#$s?BE#+$#I#$#;s?2&#>#:#5s?2&#>#:#5s?2&#>#:#5s?2&#>#:#5s?2'#?#N#;#As?2'#?#B#C#;s?2#s@:s@9##s@Ls@<#%s@M'#j#AD#j#IIs#*)s@Ps#~&s+>s#~#s@As@@s#z#s@Ss@C#%s@T%#m#'#H)#s'Cs'CE&s+D3#s@Gs@F1#s@Ys@I#%s@Z%#m#'#j#II#U#Ej#II#;3#s'=s'3s'3s'.s'.s&}s&tEl#As@DD#nI#$#IFE#&#s#)$#Ms?_$#Ms?_nD#$#GFs@F#+$#I#$#;s?`&#>#:#5s?`&#>#:#5s?`&#>#:#5s?`&#>#:#5s?`'#?#N#;#As?`'#?#B#C#;s?`&s,I#nI#$#Is?\E#&#s#'$#Ms?L$#Ms?LnD#$#$s?]s@I#+$#I#$#;s?M&#>#:#5s?M&#>#:#5s?M&#>#:#5s?M&#>#:#5s?M'#?#N#;#As?M'#?#B#C#;s?M#s@Us@T##s@gs@W#%s@h'#m#+#,s$=s#'#El#5s,lC#0Hs?ks+x'#nI#$#IFE#&##$#Ms+t$#Ms+tnD#$#GFs,o#+$#I#$#;s+q&#>#:#5s+n&#>#:#5s+n&#>#:#5s+n&#>#:#5s+n'#?#N#;#As+h'#?#B#C#;s+h&s,K#$s@qs@a's?f$s@as@`#s@_nI#$#Is?kE#&##$#Ms+f$#Ms+fnD#$#$s?ls,t#+$#I#$#;s+d&#>#:#5s+b&#>#:#5s+b&#>#:#5s+b&#>#:#5s+b'#?#N#;#As+\'#?#B#C#;s+\#s@ds@c##s@vs@f#%s@w)#m#/#0Hs?xs?x'#nI#$#IFE#&##$#Ms+.$#Ms+.nD#$#GFs;<#+$#I#$#;s+-&#>#:#5s+,&#>#:#5s+,&#>#:#5s+,&#>#:#5s+,'#?#N#;#As+''#?#B#C#;s+'&s,N#$s@~s@n's?s$s@ns@m#s@lnI#$#Is?xE#&##$#Ms+&$#Ms+&nD#$#$s?ys;A#+$#I#$#;s+%&#>#:#5s+$&#>#:#5s+$&#>#:#5s+$&#>#:#5s+$'#?#N#;#As*z'#?#B#C#;s*z#s@qs@p##sA's@s#%sA()#j#5C#nI#$#IFE#&#.$#Ms*q$#Ms*qnD#$#GFs;8#+$#I#$#;s2O&#>#:#5s2N&#>#:#5s2N&#>#:#5s2N&#>#:#5s2N'#?#N#;#As2M'#?#B#C#;s2M&s,O#nI#$#Is@%E#&#,$#Ms*n$#Ms*nnD#$#$s@&s;;#+$#I#$#;s*m&#>#:#5s*l&#>#:#5s*l&#>#:#5s*l&#>#:#5s*l'#?#N#;#As*g'#?#B#C#;s*g#s@zs@y##sA0s@|#%sA1'#j#5C#nI#$#IFE#&#7$#MG$#MGnD#$#GFE#+$#I#$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s+~#nI#$#Is@.E#&#5$#Ms+1$#Ms+1nD#$#$s@/E#+$#I#$#;s+V&#>#:#5s*q&#>#:#5s*q&#>#:#5s*q&#>#:#5s*q'#?#N#;#As*Y'#?#B#C#;s*Y#sA'sA&##sA9sA)#%sA:'#j#AD#&s+:+nI#$#Is@5E#&#<$#Ms*w$#Ms*w#sA-sA,##sA?sA/#%sA@&#j#II#)sABs#'&s+es#'#sA3sA2s###sAEsA5#%sAF%#m#'#H)#s*Es*EE&s+k8#sA9sA86#sAKsA;#%sAL%#m#'#j#II#U#Ej#II#;8#s*<s*+s*+s*&s*&s)os)fEl#As;nD#nD#$#GFs;o#+$#IB$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#N#;#AG'#?#B#C#;G&s-%#nI#$#Is@ME#&#s#4$#Ms,?$#Ms,?nD#$#$s@Ns;r#+$#I#$#;s,v&#>#:#5s+u&#>#:#5s+u&#>#:#5s+u&#>#:#5s+u'#?#N#;#As+Q'#?#B#C#;s+Q#sAFsAE##sAXsAH#%sAY'#m#*#nI#$#IFE#&#s#?$#Ms@Y$#Ms@YnD#$#GFE#+$#I#$#;s@Z&#>#:#5s@Z&#>#:#5s@Z&#>#:#5s@Z&#>#:#5s@Z'#?#N#;#As@Z'#?#B#C#;s@Z&s,J#nI#$#Is@VE#&#s#=$#Ms@F$#Ms@FnD#$#$s@WE#+$#I#$#;s@G&#>#:#5s@G&#>#:#5s@G&#>#:#5s@G&#>#:#5s@G'#?#N#;#As@G'#?#B#C#;s@G#sAOsAN##sAasAQ#%sAb'#j#AD#&s+b+#sATsAS)#sAfsAV#%sAg%#j#II#H#s#$s)]s)]E&s,01%sAk#'m#%#j#II#U#Ej#II#;/#s)Us)Ks)Ks)Fs)Fs):s)1El#As<1D#nD#$#GFs<2#+$#I9$#;s@p&#>#:#5s@p&#>#:#5s@p&#>#:#5s@p&#>#:#5s@p'#?#N#;#As@p'#?#B#C#;s@p&s-D#nD#$#$s@ls<4#+$#I8$#;s@\&#>#:#5s@\&#>#:#5s@\&#>#:#5s@\&#>#:#5s@\'#?#N#;#As@\'#?#B#C#;s@\#sAdsAc##sAvsAf#%sAw&#m#)#,s#IA#El#5s,~C#nI#$#IFE#&#s#_$#Ms,{$#Ms,{nD#$#GFsA`#+$#I#$#;s-'&#>#:#5s,v&#>#:#5s,v&#>#:#5s,v&#>#:#5s,v'#?#N#;#As,I'#?#B#C#;s,I&s-c#nI#$#Is@vE#&#s#]$#Ms,m$#Ms,mnD#$#$s@wsAc#+$#I#$#;s,s&#>#:#5s,h&#>#:#5s,h&#>#:#5s,h&#>#:#5s,h'#?#N#;#As,A'#?#B#C#;s,A#sAosAn##sB%sAq#%sB&'#m#+#&s-Ks#*%sB)#s#&j#AD#j#II>&s,us#l%sB-#s#Fm#s#J#H&#s(xs(xE&s,ys#3%sB1#s#)m#%#j#II#U#Ej#II#;.#s(ps(fs(fs(as(as(Ts(KEl#AsAwD#nD#$#GFsAx#+$#Is#;$#;sA6&#>#:#5sA6&#>#:#5sA6&#>#:#5sA6&#>#:#5sA6'#?#N#;#AsA6'#?#B#C#;sA6&s-{#nD#$#$sA2sAz#+$#Is#:$#;s@~&#>#:#5s@~&#>#:#5s@~&#>#:#5s@~&#>#:#5s@~'#?#N#;#As@~'#?#B#C#;s@~#sB*sB)##sB<sB,#%sB=&#m#)#,s#t:#El#5s.AC#nI#$#IFE#&#s$%$#Ms-G$#Ms-GnD#$#GFs.B#+$#I#$#;s-D&#>#:#5s-A&#>#:#5s-A&#>#:#5s-A&#>#:#5s-A'#?#N#;#As-;'#?#B#C#;s-;&s-z#nI#$#IsA<E#&#s$#$#Ms-7$#Ms-7nD#$#$sA=s.E#+$#I#$#;s-5&#>#:#5s-3&#>#:#5s-3&#>#:#5s-3&#>#:#5s-3'#?#N#;#As--'#?#B#C#;s--#sB5sB4##sBGsB7#%sBH'#m#+#,s&*s$0#El#5s-)C#0HsAKs.['#nI#$#IFE#&##$#Ms-P$#Ms-PnD#$#GFs<}#+$#I#$#;s&H&#>#:#5s-U&#>#:#5s-U&#>#:#5s-U&#>#:#5s-U'#?#N#;#As-N'#?#B#C#;s-N&s.l#$sBQsBA'sAF$sBAsB@#sB?nI#$#IsAKE#&##$#Ms-C$#Ms-CnD#$#$sALs=&#+$#I#$#;s&F&#>#:#5s-G&#>#:#5s-G&#>#:#5s-G&#>#:#5s-G'#?#N#;#As-B'#?#B#C#;s-B#sBDsBC##sBVsBF#%sBW)#m#/#,s-<s&F#El#5s-pC#-KJKs->KAL#-L$(H#sA^nC#$##sB`%#%###sA_-s-@K(H#sAanC#$##sBcs-A#%###sAb0H&#'#nI#$#IFE#&##$#Ms&_$#Ms&_MKLA#s5-?S'G%.S%S#s==s-M$s.sL#nC#$##F##%#G#sAjnC#$##F'#%###sAknD#$#GFs/7#+$#I*$#;#&#>#:#5s-p&#>#:#5s-p&#>#:#5s-p&#>#:#5s-p'#?#N#;#As-t'#?#B#C#;s-t&6#$sBpsB`.sAe$sB`sB_#sB^nI#$#IsAjE#&##$#Ms&d$#Ms&d(Hs/3sAr$sBtsBd#sAi$sBdsBc#sBbnC#$#4sAn-#%###sA^nC#$##sAo1#%###sA_nD#$#$sAps/A#+$#I($#;#&#>#:#5s-h&#>#:#5s-h&#>#:#5s-h&#>#:#5s-h'#?#N#;#As-k'#?#B#C#;s-k#sBhsBg##sBzsBj#%sB{.#m#s#$#nI#$#IsAuE#&#.$#Ms.S$#Ms.S>s/*L/#2$.S%S#s=Ss-c:$#9nC#$#4sAz##%#/#sAjnC#$##sA{=#%###sAknD#$#$sA|s/M#+$#I)$#;#&#>#:#5s.e&#>#:#5s.e&#>#:#5s.e&#>#:#5s.e'#?#N#;#As.P'#?#B#C#;s.P#sBtsBs##sC*sBv#%sC+:#m#.#ES#USR#UScS#Ds/Ns/Ms.I&$#As/3SBES.T#S%s/3s/Ns/2s/;Ms/1nC#$##F##%#G#sB2nC#$##F&#%###sB3nI#$#IFE#&#s#/$#M#$#M#As#.SBTs=aS#s=fs-vs#-s/@Ls#,nC#$##F##%#G#sB7nC#$##F%#%###sB8As/GSBTsBwS.sB|s/Fs/Es/DOs/CnC#$##F##%#G#sB;nC#$##F%#%###sB<As/9SBTs6PS*s=\s7#s6~s/HPs/8nC#$##F##%#G#sB?nC#$##F%#%###sB@nD#$#GFs/h#+$#I/$#;+&#>#:#5'&#>#:#5'&#>#:#5'&#>#:#5''#?#N#;#A#'#?#B#C#;#&s#G#%sCE#=m#8#6<S-S'S)S(s#JPQ&s#K#7S#S-S'S)S(s#LsC6Q#sC9sC8##sCKsC;#%sCL&#m#)#j#&s/p#j#QI#j#@I#V#JEj#QI#j#@I#VSSJE<#nS7$D$#$S8##%$#%s/y#S9VSSKJ(H#sBW)sCY#&%G$sC[sCK%sBP$sCKsCJ#sCI#sCLsCK##sC^sCN#%sC_'#m#)#m##$m##%6s#8S-S'S)S(.PQ&/#7S#S-S'S)S(0sCRQ#sCUsCT##sCgsCW#%sCh&#m#)#j#&6#j#RI#j#SD#V#JEj#TI#j#AD#WSTKJE<#=Es/r%CS$#nS7$D$#$S8%#%$#%##S9WSTLKJ(H#sBu)sCw#&%G$sCysCi%sBn$sCisCh#sCg#sCjsCi##sC|sCl#%sC}'#m#)#m##$m##%6s#QS%S#S-S'.S$S(&/#7S.S%S#S-S'0sCpS(#sCssCr##sD)sCu#%sD*&#m#)#j#&6#j#UI#j#VI#j#SD#W#KJEj#QI#j#@I#j#AD#VSCJE<#nS7$D$#$S8##%$#%s>b#S9VSCKJ6s>aS#S-S'S)#QS$&$#7S%S#S-S'S)%sD'S$#sD*sD)##sD<sD,#%sD=&#k#&*#k#;D#j#*S1#VSCs>`E<#nS7$D$#$S8##%$#%s>]#S9VSCsCtJ(H#sCD)sDF#&%G$sDHsD8%sC=$sD8sD7#sD6#sD9sD8##sDKsD;#%sDL'#m#)#m##$m##%6s7`S*S.S%S#.S)S'&/#7S&S*S.S%S#0sD?S'#sDBsDA##sDTsDD#%sDU&#m#)#j#&6#j#WD#j#XI#j#YD#V#JEj#8I#j#9D#N@#Ej#:S1#V#JEj#;D#j#:S1#XSULKJE<#nS7$D$#$S8##%$#%s?##S9XSUMLKJ(H#sCf)sDh#&%G$sDjsDZ%sC_$sDZsDY#sDX#sD[sDZ##sDmsD]#%sDn'#m#)#m##$m##%6s8&S*S.S%S#.S)S'&/#7S&S*S.S%S#0sDaS'#sDdsDc##sDvsDf#%sDw&#m#)#j#&6#j#ZD#j#[S1#j#\D#j#]S1#X#LKJEj#,D#j#^S1#j#0D#j#_S1#+KJE<#nS7$D$#$S8##%$#%sDg#S9+LKJ6sDfS.S%S#S-#S(S)&$#7S*S.S%S#S-%sDvS)#sDysDx##sE/sD{#%sE0&#k#&*#k#`I#k#;D#j#*S1#+sDeJE<#nS7$D$#$S8##%$#%sDb#S9+sD`LK6sD_S,S+S&S*#ES%&$#7S5S,S+S&S*%sE(S%#sE+sE*##sE=sE-#%sE>&#j#+C#+JEOj#;D#j#:S1#F#POEsCtS+'#@s?I%sCmsCvsClPOM'#nC#$##FsCt#%#G##ES<+JEQj#;D#j#:S1#@&#s><sC0s>;S$QP'#nC#$##Fs7h#%#G##ES>+JES$j#;D#j#:S1#@&#s=ms=ls=kS(S$Q'#nC#$##Fs7k#%#G##nD#$#<FL#+$#=4$#;1&#>#:#5*&#>#:#5*&#>#:#5*&#>#:#5*'#?#@#;#A#'#?#B#C#;#+JEMj#;D#j#:S1#@sE$#sDosDksDbOMLnR$H$#$F##%#s7m%#B#Ds?MnC#$##Fs7o#%#G##nC#$#+FsDq#%#)##&s#(#$sE_sEO>sDT$sEOsEN#sEM+sD:ML(H#sDa$sEcsES#sDX$sESsER#sEQ*s#%S:sD1sD:sD0POM$sEfsEV#sD[$sEVsEU#sETnC#$##sD`sD9#%#&##+sCOPO(H#sDi$sEksE[#sD`$sE[sEZ#sEY*s#$S<s>]sCQs>\S$QP$sEnsE^#sDc$sE^sE]#sE\nC#$##sDhs8.#%#&##+sB\QP(H#sDq$sEssEc#sDh$sEcsEb#sEa*s#%S>s>3s>2s>1S(S$Q$sEvsEf#sDk$sEfsEe#sEdnC#$##sDps82#%#&##nD#$#<sDqL#+$#=;$#;3&#>#:#5+&#>#:#5+&#>#:#5+&#>#:#5+'#?#@#;#A#'#?#B#C#;#.S5S,sE3sE/sE&OML(Hs#EsDz$sE|sEl#sDq$sElsEk#sEj*s#'S5sE7sE3sE*OMLnC#$#4sDws7|#%#$#sDgnR$H$#$sDx$#%##%#B#Ds?JnC#$##sDy)#%#&##nC#$##sDzsE:#%#+##nC#$#4sD{s7z#%#(#sDknR$H$#$sD|(#%##%#B#Ds?NnC#$##sD}s3W#%#*##nC#$##sD~sE>#%#&###sEvsEu##sF,sEx#%sF-s#-#j#5sEE#VSHES5j#Hs?G#Qs#MsDYsDbsDXPOM'#nC#$##FsD`#%#G##Rs#Gs?$sCts?#S$QP'#nC#$##Fs8P#%#G##Ss#Cs>Qs>Ps>OS(S$Q'#nC#$##Fs8O#%#G##nD#$#<FL#+$#=s#T$#;)&#>#:#5&&#>#:#5&&#>#:#5&&#>#:#5&'#?#@#;#A#'#?#B#C#;#[Es#@sEPsELsECOMLnR$H$#$F##%#s3X%#B#Ds@.nC#$##Fs3k#%#G##nC#$#+FsER#%#&##&s#e#%sF@#6j#Ds?Q#+JEPj#;D#j#:S1#F#QPEsDGS,'#*%S?s@EsDIs@DQPO'#nC#$##FsDH#%#G##'s#3nC#$##Fs8a#%#G##+JES(j#;D#j#:S1#*#S;s<Bs<As<@S)S(S$'#nC#$##Fs8:#%#G##nD#$#<FM#+$#=.$#;+&#>#:#5)&#>#:#5)&#>#:#5)&#>#:#5)'#?#@#;#A#'#?#B#C#;#nR$H$#$Fs#L#%#s88%#B#Ds@EnC#$##Fs8:#%#G##nC#$#+FE#%#%##&s#S#$sFWsFG4sEL$sFGsFF#sFE+sD]OM(H#sEY$sF[sFK#sEP$sFKsFJ#sFI$sF]sFM8sER$sFMsFL#sFKnC#$##sEWsD^#%#%##+sC;S$Q(H#sE`$sFbsFR#sEW$sFRsFQ#sFP$sFdsFT7sEY$sFTsFS#sFRnC#$##sE^s8O#%#%##nD#$#<sE_M#+$#=1$#;*&#>#:#5s#M&#>#:#5s#M&#>#:#5s#M&#>#:#5s#M'#?#@#;#A#'#?#B#C#;#nC#$#4sE`s8=#%#s#b#sEPnR$H$#$sEas#b#%##%#B#Ds@3nC#$##sEbs8?#%#s#d##nC#$##sEcE#%#&##nC#$#4sEds8R#%#s#f#sETnR$H$#$sEes#f#%##%#B#Ds@7nC#$##sEfs8T#%#s#h##nC#$##sEgE#%#&###sF_sF^##sFqsFa#%sFr>#j#5C#Fs$+S$QEsDXS5'#'s#gnC#$##FJ#%#G##nC#$##FL#%#G#s#*+JES)j#;D#j#:S1#/S>2S>?S<*&SK%$#S'S)S('#nC#$##FM#%#G##nD#$#<FO#+$#=/$#;-&#>#:#5,&#>#:#5,&#>#:#5,&#>#:#5,'#?#@#;#A#'#?#B#C#;#&s#,#$sG(sFt2sEy$sFtsFs#sFrnC#$##sE~J#%#s#x#s#unC#$##sF#L#%#s#&#s#$+s>]S(S$(H#sF,$sG.sFz#sF#$sFzsFy#sFx$sG0sF|/sF%$sF|sF{#sFznC#$##sF*M#%#%##nD#$#<sF+O#+$#=,$#;+&#>#:#5*&#>#:#5*&#>#:#5*&#>#:#5*'#?#@#;#A#'#?#B#C#;##sG#sF~##sG5sG%#%sG61#j#5C#+sE<EMnD#$#<FE#+$#=B$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&$#+sD}JO(H#sF;$sG=sG-#sF2$sG-sG,#sG++sCvLQ(H#sF?$sGAsG1#sF6$sG1sG0#sG/+s>tMS$(H#sFC$sGEsG5#sF:$sG5sG4#sG3nD#$#<sF?E#+$#=@$#;+&#>#:#5'&#>#:#5'&#>#:#5'&#>#:#5''#?#@#;#A#'#?#B#C#;##sG7sG6##sGIsG9#%sGJ2#j#AD#)sGLs#6+sE3s?:O&#s#7#sG>sG=s#(#sGPsG@#%sGQ%#m#(#j#II#U#Ej#II#+sE<s?9O(H#sFV)sGX#&%G$sGZsGJ%sFO$sGJsGI#sGH#sGKsGJ##sG]sGM#%sG^'#m#)#j#;N#U#Ej#;N#+s7{s?7S((H#sFc)sGe#&%G$sGgsGW%sF\$sGWsGV#sGU#sGXsGW##sGjsGZ#%sGk'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#+s80s?6S((H#sFt)sGv#&%G$sGxsGh%sFm$sGhsGg#sGf#sGisGh##sG{sGk#%sG|'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#+s8As?5S((H#sG))sH+#&%G$sH-sGy%sF~$sGysGx#sGw#sGzsGy##sH0sG|#%sH1'#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#+s8Rs?4S((H#sG:)sH<#&%G$sH>sH.%sG3$sH.sH-#sH,#sH/sH.##sHAsH1#%sHB'#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#+s7zs?2S'(H#sGK)sHM#&%G$sHOsH?%sGD$sH?sH>#sH=#sH@sH?##sHRsHB#%sHS'#m#)#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#+s81s?1S'(H#sG^)sH`#&%G$sHbsHR%sGW$sHRsHQ#sHP#sHSsHR##sHesHU#%sHf'#m#)#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s$(s#zs#ms#\s#Ks#:s#)6#MnD#$#<FM#+$#=s%.$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&s%p#nD#$#<sGlM#+$#=s$z$#;s$v&#>#:#5s%^&#>#:#5s%^&#>#:#5s%^&#>#:#5s%^'#?#@#;#As$o'#?#B#C#;s$o#sHdsHc##sHvsHf#%sHw&#m#)#*s&0S<sAisF]sAhS$QJ'#*s%/S;s>ns>ms>lS)S(L'#*s$`SKs$_s$^s$]S'S)M'#nD#$#<FE#+$#=s$h$#;'&#>#:#5%&#>#:#5%&#>#:#5%&#>#:#5%'#?#@#;#A#'#?#B#C#;#&s$J#$sI%sHq*sGv$sHqsHp#sHo$sI'sHs*sGx$sHssHr#sHq$sI)sHu*sGz$sHusHt#sHsnD#$#<sH#E#+$#=s$`$#;'&#>#:#5%&#>#:#5%&#>#:#5%&#>#:#5%'#?#@#;#A#'#?#B#C#;##sHwsHv##sI-sHy#%sI.,#j#AD#*s&CS<sA|sFpsA{S$Qs@o)sI1#'$&s$;#$sI4sI$&sH)$sI$sI##sH~#sI%sI$##sI7sI'#%sI8'#m#*#j#;N#U#Ej#;N#+JES'j#;D#j#:S1#*#S=s>Hs>Gs>FS-S's@p)sIA#'$&s$>#$sIDsI4&sH9$sI4sI3#sI2#sI5sI4##sIGsI7#%sIH'#m#*#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#*4S=s>Ys>Xs>WS-S's@o)sIR#'$&s$>#$sIUsIE&sHJ$sIEsID#sIC#sIFsIE##sIXsIH#%sIY'#m#*#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#*s#%S=s>js>is>hS-S's@n)sIc#'$&s$>#$sIfsIV&sH[$sIVsIU#sIT#sIWsIV##sIisIY#%sIj'#m#*#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#*s#6S=s>{s>zs>yS-S's@m)sIt#'$&s$>#$sIwsIg&sHl$sIgsIf#sIe#sIhsIg##sIzsIj#%sI{'#m#*#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#+JES#j#;D#j#:S1#/S=2S=?SK*&SV%$#S%S#s@q)sJ/#'$&s$D#$sJ2sI~&sI'$sI~sI}#sI|#sJ#sI~##sJ5sJ%#%sJ6'#m#*#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#*9SV876S%S#s@p)sJB#'$&s$D#$sJEsJ5&sI:$sJ5sJ4#sJ3#sJ6sJ5##sJHsJ8#%sJI'#m#*#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s$'s%]s#vs#bs#Qs#@s#/6#MnD#$#<FM#+$#=s&m$#;s&k&#>#:#5s&i&#>#:#5s&i&#>#:#5s&i&#>#:#5s&i'#?#@#;#As&c'#?#B#C#;s&c&s'S#nD#$#<sIOM#+$#=s&]$#;s&W&#>#:#5s'>&#>#:#5s'>&#>#:#5s'>&#>#:#5s'>'#?#@#;#As&P'#?#B#C#;s&P#sJGsJF##sJYsJI#%sJZ&#m#)#,s&'s$B#El#5sIjC#'s'WnC#$##FsI0#%#G##nC#$##Fs<z#%#G#s&HnD#$#<FL#+$#=s'{$#;$&#>#:#5#&#>#:#5#&#>#:#5#&#>#:#5#'#?#@#;#As&t'#?#B#C#;s&t&s(,##sJRsJQs'H#sJdsJT#%sJe%#m#+#nR$H$#$Fs&~#%#sGq%#B#DsDYnC#$##FE#%#G##&s&n#nC#$#4sIbE#%#s&l#sIRnR$H$#$sIcs'&#%##%#B#DsD5nC#$##sIdE#%#s&n###sJ\sJ[##sJnsJ^#%sJo(#j#5C#)sJqs'm&s'oG#sJbsJas'm#sJtsJd#%sJu%#m#'#&s'ls?3%sJx#s?0j#DsJy#&s'#sIx%sJ{#s?-m#s?1#&s&SsDo%sJ~#s?*m#s?.#j#DsK$#j#'H#V#JEj#DsK'#j#'H#YSIH.+#El#Ds(#sK*#nR$H$#$Fs($#%#sJ)%#B#DsDy&s()#nR$H$#$sJ%s(&#%#sIq%#B#DsDS#sJysJx##sK/sJ{#%sK0&#m#)#,@:#El#5s8aC#nR$H$#$Fs'p#%#s8P%#B#DsE&nC#$##Fs8c#%#G##&s(\#nC#$#4sJ/s8e#%#s't#sI{nR$H$#$sJ0s't#%##%#B#DsD^nC#$##sJ1s8g#%#s'v###sK)sK(##sK;sK+#%sK<(#m#,#,s')s#6#El#5sJhC#+sFvKJFs(FOMEsJRS&'#'s(#nC#$##FsJQ#%#G##nD#$#<FK#+$#=%$#;#&#>#:#5s'Z&#>#:#5s'Z&#>#:#5s'Z&#>#:#5s'Z'#?#@#;#As#C'#?#B#C#;s#C+JELj#;D#j#:S1#*#S,sJvsF{sFrMLKnR$H$#$F##%#s8U%#B#DsE<nC#$##Fs8W#%#G##nC#$#+FsJu#%#)##&/#$sKNsK>/sJC$sK>sK=#sK<$sKPsK@s(0sJE$sK@sK?#sK>nC#$##sJJsJ_#%#s(3##nD#$#<sJKK#+$#=&$#;#&#>#:#5s'R&#>#:#5s'R&#>#:#5s'R&#>#:#5s'R'#?#@#;#As(A'#?#B#C#;s(A(H6sJS$sKUsKE#sJJ$sKEsKD#sKCnC#$#4sJOs8[#%###sJ?nR$H$#$sJP1#%##%#B#DsD~nC#$##sJQs8]#%#%##nC#$##sJRsK'#%#)##nC#$#4sJSs8g#%#'#sJCnR$H$#$sJT5#%##%#B#DsE&nC#$##sJUs8i#%#)##nC#$##sJVsK+#%#&###sKNsKM##sK`sKP#%sKa6#m#s#%#nC#$#4sJ[s8[#%#/#sJKnR$H$#$sJ\=#%##%#B#DsE.nC#$##sJ]s8i#%#1##nC#$##sJ^sK3#%#5##nC#$#4sJ_s8\#%#3#sJOnR$H$#$sJ`A#%##%#B#DsE2nC#$##sJas8u#%#5##nC#$##sJbsK7#%#&###sKZsKY##sKlsK\#%sKmB#m#.#USJsFeUSNS,DsE%s(Cs(2%$#DsK-sK,s(F#sFgsFf's(wnC#$##FsK%#%#G##@sEts(3sEssIwsErQPO'#nC#$##FsIv#%#G##nD#$#<FK#+$#=s#8$#;&&#>#:#5#&#>#:#5#&#>#:#5#&#>#:#5#'#?#@#;#As),'#?#B#C#;s),@sFos#3sKJsGOsGFMLKnR$H$#$F##%#s8`%#B#DsElnC#$##Fs8b#%#G##nC#$#+FsKI#%#&##&s#?#%sK~#4m#/#6sFvS+S&S*S.s#BsKMS#&s#C#7S,S+S&S*S.s#DsKoS##sKrsKq##sL(sKt#%sL)&#m#)#DCsKTs)J#S-Ej#&s)S#j#aI#j#<D#j#7I#j#%D#V#JEj#8I#j#9D#Ns)^#Ej#:S1#W#KJEj#`I#j#;D#j#:S1#5JE<#nS7$D$#$S8##%$#%sFh#S95KJ6sFgS#S-S'S)#QS$&$#7S%S#S-S'S)%sL-S$#sL0sL/##sLBsL2#%sLC&#k#&*#k#;D#j#*S1#5sFfE<#nS7$D$#$S8##%$#%sFc#S95sH$K6sFaS&S*S.S%#ES-&$#7S+S&S*S.S%%sL:S-#sL=sL<##sLOsL?#%sLP&#j#+C#FS3OMEsH(S*'#@sGJS3sL%sH*sG}OML'#nC#$##FsF_#%#G##@sF[S3sK#sK,sJ~QPO'#nC#$##FsF^#%#G##@sFYS3sFXsJ\sFWS$QP'#nC#$##FsF\#%#G##nD#$#<FK#+$#=,$#;)&#>#:#5&&#>#:#5&&#>#:#5&&#>#:#5&'#?#@#;#A#'#?#B#C#;#@sFtS3sFksFVsFUMLKnR$H$#$F##%#sFS%#B#DsFQnC#$##FsFV#%#G##nC#$#+FsFm#%#&##&:#$sLcsLS3sKX$sLSsLR#sLQ5sL1L(H#sKe$sLgsLW#sK\$sLWsLV#sLU*S3S,sL:sH?sH6OML$sLjsLZ#sK_$sLZsLY#sLXnC#$##sKdsFu#%#&##5sJqO(H#sKm$sLosL_#sKd$sL_sL^#sL]*S3S:sK=sKFsK<QPO$sLrsLb#sKg$sLbsLa#sL`nC#$##sKlsFy#%#&##5sJ[P(H#sKu$sLwsLg#sKl$sLgsLf#sLe*S3S?sFwsJ{sFvS$QP$sLzsLj#sKo$sLjsLi#sLhnC#$##sKtsF|#%#&##nD#$#<sKuK#+$#=;$#;3&#>#:#5+&#>#:#5+&#>#:#5+&#>#:#5+'#?#@#;#A#'#?#B#C#;#(Hs#6sK}$sM#sLo#sKt$sLosLn#sLm*S3S+sG2sFysFxMLKnC#$#4sKzsFO#%#$#sKjnR$H$#$sK{$#%##%#B#DsFMnC#$##sK|sFV#%#&##nC#$##sK}sG5#%#*##nC#$#4sK~sFK#%#(#sKnnR$H$#$sL#(#%##%#B#DsFQnC#$##sL$sFN#%#*##nC#$##sL%sG9#%#&###sLysLx##sM/sL{#%sM0s#,#j#5sLH#QS3sL_sHdsH[OML'#nC#$##FsG=#%#G##RS3sK]sKfsK\QPO'#nC#$##FsG<#%#G##SS3sG6sK:sG5S$QP'#nC#$##FsG:#%#G##nD#$#<FK#+$#=s#F$#;)&#>#:#5&&#>#:#5&&#>#:#5&&#>#:#5&'#?#@#;#A#'#?#B#C#;#[ES3sGIsG4sG3MLKnR$H$#$F##%#sF?%#B#DsG/nC#$##FsF`#%#G##nC#$#+FsGK#%#&##&s#T#%sMA#4j#DsFR#FS3POEsLTS&'#*S3S5sLZsLVsLMPOM'#nC#$##FsF@#%#G##'s#-nC#$##FsGI#%#G##*S3S<sF:sK.sF9S(S$Q'#nC#$##FsF=#%#G##nD#$#<FL#+$#=+$#;(&#>#:#5&&#>#:#5&&#>#:#5&&#>#:#5&'#?#@#;#A#'#?#B#C#;#nR$H$#$Fs#C#%#sF7%#B#DsG@nC#$##FsF9#%#G##nC#$#+FE#%#%##&s#J#$sMRsMB1sLG$sMBsMA#sM@5sL-M(H#sLT$sMVsMF#sLK$sMFsME#sMD$sMXsMH5sLM$sMHsMG#sMFnC#$##sLRsFS#%#%##5sJFQ(H#sL[$sM]sMM#sLR$sMMsML#sMK$sM_sMO7sLT$sMOsMN#sMMnC#$##sLYsFR#%#%##nD#$#<sLZL#+$#=1$#;*&#>#:#5s#D&#>#:#5s#D&#>#:#5s#D&#>#:#5s#D'#?#@#;#A#'#?#B#C#;#nC#$#4sL[sF6#%#s#Y#sLKnR$H$#$sL\s#Y#%##%#B#DsG.nC#$##sL]sF8#%#s#[##nC#$##sL^E#%#&##nC#$#4sL_sFQ#%#s#]#sLOnR$H$#$sL`s#]#%##%#B#DsG2nC#$##sLasFS#%#s#_##nC#$##sLbE#%#&###sMZsMY##sMlsM\#%sMm>#j#5C#FS3QPEsLDS+'#'s#^nC#$##FJ#%#G##nC#$##FL#%#G#s#**S3S>sF2sF1sF0S)S(S$'#nC#$##FM#%#G##nD#$#<FM#+$#=)$#;'&#>#:#5&&#>#:#5&&#>#:#5&&#>#:#5&'#?#@#;#A#'#?#B#C#;#&s#&#$sMysMi,sLn$sMisMh#sMgnC#$##sLsJ#%#s#i#s#fnC#$##sLtL#%#@#>5sJXS$(H#sL}$sN#sMo#sLt$sMosMn#sMm$sN%sMq/sLv$sMqsMp#sMonC#$##sL{M#%#%##nD#$#<sL|M#+$#=,$#;+&#>#:#5*&#>#:#5*&#>#:#5*&#>#:#5*'#?#@#;#A#'#?#B#C#;##sMtsMs##sN*sMv#%sN+1#j#5C#5sLbEnD#$#<FE#+$#=<$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&$#5sL4J(H#sM0$sN2sM~#sM'$sM~sM}#sM|5sJ{L(H#sM4$sN6sN&#sM+$sN&sN%#sN$5sJoM(H#sM8$sN:sN*#sM/$sN*sN)#sN(nD#$#<sM4E#+$#=@$#;+&#>#:#5'&#>#:#5'&#>#:#5'&#>#:#5''#?#@#;#A#'#?#B#C#;##sN,sN+##sN>sN.#%sN?2#j#AD#)sNAs#05sLFsF/&#s#1#sN3sN2s#(#sNEsN5#%sNF%#m#(#j#II#U#Ej#II#5sLOsF.(H#sMK)sNM#&%G$sNOsN?%sMD$sN?sN>#sN=#sN@sN?##sNRsNB#%sNS'#m#)#j#;N#U#Ej#;N#5sF-sF,(H#sMX)sNZ#&%G$sN\sNL%sMQ$sNLsNK#sNJ#sNMsNL##sN_sNO#%sN`'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#5sF>sF+(H#sMi)sNk#&%G$sNmsN]%sMb$sN]sN\#sN[#sN^sN]##sNpsN`#%sNq'#m#)#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#5sFOsF*(H#sMz)sN|#&%G$sN~sNn%sMs$sNnsNm#sNl#sNosNn##sO%sNq#%sO&'#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#5sF`sF)(H#sN/)sO1#&%G$sO3sO#%sN($sO#sN~#sN}#sO$sO###sO6sO&#%sO7'#m#)#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#5sF(sF'(H#sN@)sOB#&%G$sODsO4%sN9$sO4sO3#sO2#sO5sO4##sOGsO7#%sOH'#m#)#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#5sF;sF&(H#sNS)sOU#&%G$sOWsOG%sNL$sOGsOF#sOE#sOHsOG##sOZsOJ#%sO['#m#)#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s$(s#zs#ms#\s#Ks#:s#)6#LnD#$#<FL#+$#=s%%$#;G&#>#:#5G&#>#:#5G&#>#:#5G&#>#:#5G'#?#@#;#AG'#?#B#C#;G&s%a#nD#$#<sNaL#+$#=s$t$#;s$p&#>#:#5s%O&#>#:#5s%O&#>#:#5s%O&#>#:#5s%O'#?#@#;#As$i'#?#B#C#;s$i#sOYsOX##sOksO[#%sOl&#m#)#*S3S:sN:sNCsN9QPJ'#*S3S<sH`sMTsH_S(S$L'#*S3S>sH0sH/sH.S)S(M'#nD#$#<FE#+$#=s$b$#;'&#>#:#5%&#>#:#5%&#>#:#5%&#>#:#5%'#?#@#;#A#'#?#B#C#;#&s$J#$sOvsOf*sNk$sOfsOe#sOd$sOxsOh*sNm$sOhsOg#sOf$sOzsOj*sNo$sOjsOi#sOhnD#$#<sNtE#+$#=s$`$#;'&#>#:#5%&#>#:#5%&#>#:#5%&#>#:#5%'#?#@#;#A#'#?#B#C#;##sOlsOk##sO~sOn#%sP#,#j#AD#*S3S:sNMsNVsNLQPsGd)sP&#'$&s$;#$sP)sOu&sNz$sOusOt#sOs#sOvsOu##sP,sOx#%sP-'#m#*#j#;N#U#Ej#;N#*S3S;sF%sF$sF#S'S)sGb)sP3#'$&s$;#$sP6sP&&sO+$sP&sP%#sP$#sP'sP&##sP9sP)#%sP:'#m#*#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#*S3S;sF6sF5sF4S'S)sGa)sPD#'$&s$;#$sPGsP7&sO<$sP7sP6#sP5#sP8sP7##sPJsP:#%sPK'#m#*#j#JD#j#KD#j#>S/#W#KJEj#5D#j#:D#j#>S/#*S3S;sFGsFFsFES'S)sG`)sPU#'$&s$;#$sPXsPH&sOM$sPHsPG#sPF#sPIsPH##sP[sPK#%sP\'#m#*#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#*S3S;sFXsFWsFVS'S)sG_)sPf#'$&s$;#$sPisPY&sO^$sPYsPX#sPW#sPZsPY##sPlsP\#%sPm'#m#*#j#JD#j#KD#j#>S0#W#KJEj#5D#j#:D#j#>S0#*S3S=sE~sE}sE|S#S-sG])sPw#'$&s$;#$sPzsPj&sOo$sPjsPi#sPh#sPksPj##sP}sPm#%sP~'#m#*#j#<D#j#;N#j#@N#j#?C#X#LKJEj#AD#j#;N#j#@N#j#?C#*S3S=sF5sF4sF3S#S-sG\)sQ.#'$&s$;#$sQ1sP}&sP&$sP}sP|#sP{#sP~sP}##sQ4sQ$#%sQ5'#m#*#j#;N#j#CI#j#'N#j#?C#X#LKJEj#;N#j#CI#j#'N#j#?C#;s#zs%Ts#ms#\s#Ks#:s#)6#LnD#$#<FL#+$#=s&[$#;s&Y&#>#:#5s&W&#>#:#5s&W&#>#:#5s&W&#>#:#5s&W'#?#@#;#As&T'#?#B#C#;s&T&s';#nD#$#<sP;L#+$#=s&N$#;s&H&#>#:#5s'&&#>#:#5s'&&#>#:#5s'&&#>#:#5s'&'#?#@#;#As&A'#?#B#C#;s&A#sQ3sQ2##sQEsQ5#%sQF&#m#)#,s%zs$9#El#5sIiC#'s'?nC#$##FsKT#%#G##nC#$##FsKQ#%#G#s&9nD#$#<FK#+$#=s'X$#;$&#>#:#5#&#>#:#5#&#>#:#5#&#>#:#5#'#?#@#;#As&b'#?#B#C#;s&b&s'b##sQ>sQ=s'0#sQPsQ@#%sQQ%#m#+#nR$H$#$Fs&l#%#sN]%#B#DsKEnC#$##FE#%#G##&s&_#nC#$#4sPNE#%#s&]#sP>nR$H$#$sPOs&p#%##%#B#DsJ}nC#$##sPPE#%#s&_###sQHsQG##sQZsQJ#%sQ[(#j#5C#)sQ]s'U&s'WG#sQNsQMs'U#sQ`sQP#%sQa%#m#'#&s'TsE{%sQd#sExj#DsQe#&s&psPd%sQg#sEum#sEy#&s&JsK[%sQj#sErm#sEv#j#DsQl#j#'H#V#JEj#DsQo#j#'H#YSIH.+#El#Ds'gsQr#nR$H$#$Fs'h#%#sPq%#B#DsKe&s'm#nR$H$#$sPms'j#%#sP]%#B#DsK?#sQesQd##sQwsQg#%sQx&#m#)#,@:#El#5sKAC#nR$H$#$Fs'Y#%#sJ~%#B#DsKnnC#$##FsKC#%#G##&s(6#nC#$#4sPwsKE#%#s']#sPgnR$H$#$sPxs']#%##%#B#DsKJnC#$##sPysKG#%#s'_###sQqsQp##sR'sQs#%sR((#m#,#,s&vs#6#El#5sLCC#5sQ\JFS3MLEsL%S.'#'s'hnC#$##FsJP#%#G##nD#$#<FJ#+$#=%$#;#&#>#:#5s'H&#>#:#5s'H&#>#:#5s'H&#>#:#5s'H'#?#@#;#As#C'#?#B#C#;s#C*S3S&sLNsEqsEpLKJnR$H$#$F##%#sEn%#B#DsL%nC#$##FsEq#%#G##nC#$#+FsLM#%#&##&,#$sR7sR',sQ,$sR'sR&#sR%$sR9sR)s'rsQ.$sR)sR(#sR'nC#$##sQ3sJ[#%#s'u##nD#$#<sQ4J#+$#=&$#;#&#>#:#5s'@&#>#:#5s'@&#>#:#5s'@&#>#:#5s'@'#?#@#;#As(&'#?#B#C#;s(&(H3sQ<$sR>sR.#sQ3$sR.sR-#sR,nC#$#4sQ8sEp#%###sQ(nR$H$#$sQ91#%##%#B#DsKgnC#$##sQ:sEr#%#%##nC#$##sQ;sL[#%#)##nC#$#4sQ<sF%#%#'#sQ,nR$H$#$sQ=5#%##%#B#DsKknC#$##sQ>sF'#%#)##nC#$##sQ?sL_#%#&###sR7sR6##sRIsR9#%sRJ6#m#B#nC#$#4sQDsEj#%#/#sQ4nR$H$#$sQE=#%##%#B#DsKsnC#$##sQFsE~#%#1##nC#$##sQGsLg#%#5##nC#$#4sQHsEi#%#3#sQ8nR$H$#$sQIA#%##%#B#DsKwnC#$##sQJsF3#%#5##nC#$##sQKsLk#%#&###sRCsRB##sRUsRE#%sRVB#m#.#DsKhsKfs't#sEgsEfDsQpsLgs(*#sEesEd's(ZnC#$##FsJ{#%#G##@sR&S3sQqsQmsQdPOM'#nC#$##FsKW#%#G##nD#$#<FJ#+$#=s#3$#;&&#>#:#5#&#>#:#5#&#>#:#5#&#>#:#5#'#?#@#;#As(d'#?#B#C#;s(d@sEpS3sL|sFCsFBLKJnR$H$#$F##%#sEb%#B#DsLSnC#$##FsEe#%#G##nC#$#+FsL{#%#&##&s#:#%sRe#2m#/#6sEwS*S.S%S#s#=sM#S'&s#>#7S&S*S.S%S#s#?sRVS'#sRYsRX##sRksR[#%sRl&#m#)#DCsM*s({#S)Ej#&s)(#j#<D#j#7I#j#%D#V#JEj#8I#j#9D#Ns)2#Ej#:S1#V#JEj#;D#j#:S1#`SdsRbsMPsEbs?Gs2*s1js1Js0ws0Ws)D#LU#Ej#&sRv#j#+C#j#/sR}#j#bH#j#cD#j#)N#j#dS1#j#3SF#j#esS)##"). Qed.

(* [comment removed for export] *)
Definition bkey (e : expr) : option nat := first_var e.
Record binfo := BI { bi_base : expr; bi_br : option (Z * Z) }.
Record ntab := NT { nt_vars : list (list (expr * positive)); nt_other : list (expr * positive); nt_next : positive; nt_info : ptree binfo }.
Definition nt_empty : ntab := NT [] [] xH PTLeaf.
Fixpoint alookupE (l : list (expr * positive)) (b : expr) : option positive :=
  match l with
  | [] => None
  | (b', id) :: rest => if expr_eqb b b' then Some id else alookupE rest b
  end.
Definition nt_bucket (t : ntab) (k : option nat) : list (expr * positive) :=
  match k with Some n => lget (nt_vars t) n | None => nt_other t end.
Definition nt_add (t : ntab) (k : option nat) (p : expr * positive) (bi : binfo) : ntab :=
  match k with
  | Some n => NT (lset (nt_vars t) n p) (nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  | None => NT (nt_vars t) (p :: nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  end.
Definition intern (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
  let k := bkey b in
  match alookupE (nt_bucket t k) b with
  | Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
  | None => let id := nt_next t in
            let bi := BI b (base_rangeB bc b) in
            (id, bi, nt_add t k (b, id) bi)
  end.

Definition NTI (bc : bctx) (t : ntab) : Prop :=
  (forall k b id, In (b, id) (nt_bucket t k) ->
     k = bkey b /\ pt_get (nt_info t) id = Some (BI b (base_rangeB bc b)) /\ (id < nt_next t)%positive)
  /\ (forall k b id id', In (b, id) (nt_bucket t k) -> In (b, id') (nt_bucket t k) -> id = id').

Lemma nt_bucket_empty : forall k, nt_bucket nt_empty k = [].
Proof. intros [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity]. Qed.
Lemma NTI_empty : forall bc, NTI bc nt_empty.
Proof. intros bc. split; intros; rewrite nt_bucket_empty in *; contradiction. Qed.

Lemma alookupE_Some : forall l b id, alookupE l b = Some id -> In (b, id) l.
Proof.
  induction l as [|[b' id'] rest IH]; cbn; intros b id H; [discriminate|].
  destruct (expr_eqb b b') eqn:E.
  - injection H as <-. apply p_expr_eqb_eq in E. subst. left. reflexivity.
  - right. apply IH. exact H.
Qed.
Lemma alookupE_None : forall l b id, alookupE l b = None -> ~ In (b, id) l.
Proof.
  induction l as [|[b' id'] rest IH]; cbn; intros b id H; [tauto|].
  destruct (expr_eqb b b') eqn:E; [discriminate|].
  intros [X|X].
  - injection X as -> ->. rewrite p_expr_eqb_refl in E. discriminate.
  - exact (IH _ _ H X).
Qed.
Lemma nt_add_bucket : forall t k p bi k',
  nt_bucket (nt_add t k p bi) k' = if okey_eqb k' k then p :: nt_bucket t k' else nt_bucket t k'.
Proof.
  intros t [n|] p bi [m|]; cbn [nt_add nt_bucket nt_vars nt_other okey_eqb]; try reflexivity. apply lget_lset.
Qed.
Lemma nt_add_next : forall t k p bi, nt_next (nt_add t k p bi) = Pos.succ (nt_next t).
Proof. intros t [n|] p bi; reflexivity. Qed.
Lemma nt_add_info : forall t k p bi, nt_info (nt_add t k p bi) = pt_set (nt_next t) bi (nt_info t).
Proof. intros t [n|] p bi; reflexivity. Qed.

Lemma intern_ok : forall bc t b id bi t',
  NTI bc t -> intern bc t b = (id, bi, t') ->
  NTI bc t' /\ bi = BI b (base_rangeB bc b) /\ In (b, id) (nt_bucket t' (bkey b))
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
  intros bc t b id bi t' [HA HB] H. unfold intern in H.
  destruct (alookupE (nt_bucket t (bkey b)) b) as [id0|] eqn:HL.
  - injection H as <- <- <-. pose proof (alookupE_Some _ _ _ HL) as HIn.
    destruct (HA _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo.
    split; [split; assumption|]. split; [reflexivity|]. split; [exact HIn|]. intros; assumption.
  - injection H as <- <- <-.
    split; [|split; [reflexivity|split]].
    + split.
      * intros k b0 id0 HIn. rewrite nt_add_bucket in HIn. rewrite nt_add_info, nt_add_next.
        destruct (okey_eqb_spec k (bkey b)) as [->|NE].
        -- destruct HIn as [X|X].
           ++ injection X as <- <-. split; [reflexivity|]. rewrite pt_gss. split; [reflexivity|lia].
           ++ destruct (HA _ _ _ X) as (H1 & H2 & H3). split; [exact H1|].
              rewrite pt_gso by lia. split; [exact H2|lia].
        -- destruct (HA _ _ _ HIn) as (H1 & H2 & H3). split; [exact H1|]. rewrite pt_gso by lia. split; [exact H2|lia].
      * intros k b0 id0 id0' H1 H2. rewrite nt_add_bucket in H1, H2.
        destruct (okey_eqb_spec k (bkey b)) as [->|NE]; [|exact (HB _ _ _ _ H1 H2)].
        destruct H1 as [X1|X1]; destruct H2 as [X2|X2].
        -- congruence.
        -- injection X1 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X2).
        -- injection X2 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X1).
        -- exact (HB _ _ _ _ X1 X2).
    + rewrite nt_add_bucket. destruct (okey_eqb_spec (bkey b) (bkey b)); [|congruence]. left. reflexivity.
    + intros k p HIn. rewrite nt_add_bucket. destruct (okey_eqb_spec k (bkey b)); [right|]; exact HIn.
Qed.

Lemma nt_same_eq : forall bc t b1 id1 b2 id2,
  NTI bc t -> In (b1, id1) (nt_bucket t (bkey b1)) -> In (b2, id2) (nt_bucket t (bkey b2)) ->
  Pos.eqb id1 id2 = expr_eqb b1 b2.
Proof.
  intros bc t b1 id1 b2 id2 [HA HB] H1 H2.
  destruct (HA _ _ _ H1) as (_ & I1 & _). destruct (HA _ _ _ H2) as (_ & I2 & _).
  destruct (Pos.eqb_spec id1 id2) as [<-|NE].
  - rewrite I1 in I2. injection I2 as <-. symmetry. apply p_expr_eqb_refl.
  - destruct (expr_eqb b1 b2) eqn:E; [|reflexivity]. exfalso. apply NE.
    apply p_expr_eqb_eq in E. subst b2. exact (HB _ _ _ _ H1 H2).
Qed.

Record stx := STX { sx_a : saddr; sx_w : nat; sx_v : expr; sx_sp : sprep; sx_bid : positive; sx_br : option (Z * Z) }.

Fixpoint mk_stxs (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=   (* [comment removed for export] *)
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxs bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      (sxs ++ [STX a w v (mk_sprepB bc (a_base a) (a_off a) (elen w)) bid (bi_br bi)], t2)
  end.

Definition obrB (bc : bctx) (K : kentry) : option (Z * Z) :=
  match kbase K with Some kb => base_rangeB bc kb | None => None end.
Definition g1cB (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
  fst (fst (prune1pcB bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Fixpoint chain_slow (bc : bctx) (sxs : list stx) (l : list kentry) : list kentry :=
  match sxs with
  | [] => l
  | sx :: rest => chain_slow bc rest (flat_map (g1cB bc sx) l)
  end.
Fixpoint chainK (bc : bctx) (sxs : list stx) (K : kentry) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK bc rest K same_of br2
      | PRepl l => chain_slow bc rest l
      end
  end.
(* [comment removed for export] *)
Fixpoint chainK2 (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK2 bc rest K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.


Fixpoint entriesV (bc : bctx) (sxs : list stx) (kn : list kentry) (t : ntab) : list kentry :=
  match kn with
  | [] => []
  | K :: rest =>
      match kbase K with
      | Some kb => let '(r, t') := intern bc t kb in
                   let '(bid, bi) := r in
                   chainK2 bc sxs K (Some kb) (Pos.eqb bid) (bi_br bi) ++ entriesV bc sxs rest t'
      | None => chainK2 bc sxs K None (fun _ => false) None ++ entriesV bc sxs rest t
      end
  end.
Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
  end.
Definition carryV (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t) := mk_stxs bc log nt_empty in
  stores_part bc sxs ++ entriesV bc sxs kn t.
(* [comment removed for export] *)
Definition carryK0 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryV bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FM (fk : list kentry) (s : sentry) (l : list kentry) : list kentry :=
  match s with SE a w v => flat_map (g1 fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v) l end.
Fixpoint chainRo (fk : list kentry) (sxo : list sentry) (l : list kentry) : list kentry :=
  match sxo with [] => l | s :: newer => chainRo fk newer (FM fk s l) end.
Definition kw (s : sentry) : kentry := match s with SE a w v => KWord a w v end.
Fixpoint SPRo (fk : list kentry) (sxo : list sentry) : list kentry :=
  match sxo with [] => [] | s :: newer => SPRo fk newer ++ chainRo fk newer [kw s] end.

Lemma flat_map_app' : forall (A B : Type) (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros. rewrite !flat_map_concat_map, map_app, concat_app. reflexivity. Qed.
Lemma FM_app : forall fk s l1 l2, FM fk s (l1 ++ l2) = FM fk s l1 ++ FM fk s l2.
Proof. intros fk [a w v] l1 l2. unfold FM. apply flat_map_app'. Qed.
Lemma chainRo_snoc : forall fk sxo s l, chainRo fk (sxo ++ [s]) l = FM fk s (chainRo fk sxo l).
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo app]. apply IH. Qed.
Lemma chainRo_app : forall fk sxo l1 l2, chainRo fk sxo (l1 ++ l2) = chainRo fk sxo l1 ++ chainRo fk sxo l2.
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo]. rewrite FM_app. apply IH. Qed.
Lemma SPRo_snoc : forall fk sxo s, SPRo fk (sxo ++ [s]) = kw s :: FM fk s (SPRo fk sxo).
Proof.
  intros fk sxo s. induction sxo as [|x rest IH]; [destruct s; reflexivity|].
  cbn [SPRo app]. rewrite IH, chainRo_snoc, FM_app. reflexivity.
Qed.

Lemma carry_vertical : forall log kn,
  carry log kn [] = (SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn, [], []).
Proof.
  intros log kn. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry rev]. pose proof (carry_facts older kn []) as HF. rewrite IH in HF |- *. cbn [fst] in HF.
  cbv beta iota zeta. rewrite !facts_of_filter in *. rewrite HF.
  rewrite p_prunepc_eq by constructor. rewrite prunep_nil.
  match goal with |- context [flat_map ?g ?l] => change (flat_map g l) with (FM (List.filter is_factb kn) (SE a w v) l) end.
  rewrite FM_app, SPRo_snoc, chainRo_snoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition strip (sx : stx) : sentry := SE (sx_a sx) (sx_w sx) (sx_v sx).
Definition SX_OK (bc : bctx) (t : ntab) (sx : stx) : Prop :=
  In (a_base (sx_a sx), sx_bid sx) (nt_bucket t (bkey (a_base (sx_a sx))))
  /\ sx_br sx = base_rangeB bc (a_base (sx_a sx))
  /\ sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)).
Scheme kc__10 := Elimination for Corelib.Init.Datatypes.option Sort Prop.

Lemma g1cB_eq : forall fk sx,
  sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) ->
  flat_map (g1cB (mkbc fk) sx) = FM fk (strip sx).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.stx); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_sp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_a); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_w); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Stdlib.Lists.List.flat_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.g1cB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.FM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.strip); constr:(@stdpp.tactics.f_equal_help); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.g1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mk_sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_v); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kbase); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1pc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1p); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1p_nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.p_prune1pc_eq); constr:(@kc__10); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB_eqf); constr:(@kc__10 (@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr))|] [|@x; @kb; @s; @br2; @hints; @K; @wv; @w; @wa; @sp; @p; @n1; @k1; @b1; @e; @o; @l; @Hsp; @sx; @fk|] "#$g#,#_###'#0#M#$#&#%#N#(#3#>#B#=#O#4#@#?#H#J#L#P#Q#K#U#C#V#X#5#<#A#)#R#T#S#W#Y#+#*#,#\#[#]#Z#^#_#`#1#G#2#6#F#8#7#9#;#:#E#/#D#I5#R&#S&#T$#U)#V$#W$#X$#Y$#Z$#[%#\$#>'#/&#;'#]$#^%#:+#<%-EUQC%G'C(#)$*C+#.(&%#$L*#%IVM#G/EE#URGVS#I#%HVM#I/EE#'I(#)$*I+#0H&%#1IYNH$)&#/EE#k##E=k##>>VOEEk##%$,#$%D'H(#)$*H+#.(&%#-S$2s#*#-S%%K'D*D1DUS&S%2PPUJ#US'G%S1VS(#CUS2'nJ$F$#$'&#%$#%$##\S).C-,+G*##10##s#:3#(0)1+10K%$#ZNK#432G$s#@(#j#&L#2:9k#'3#k#(;#k#)E#k#*F#k#+S3#k#,S4#k#-L#US*D.A210[C#A@?G>7#s#%s#$##s#Ns#'#$s#O#2j#.)#k#/FLk#0P#k#1F#US+DWC<;:3K#s#+s#*s#)Gs#(A#s#/s#.##s#Xs#1#$s#Y#<j#&)#k#2Fs#+US,DUGCnJ$F$#$s#.s#-#%$#%##s#*3Ks##s#4s#3s#2Gs#1##s#8s#7##s#as#:#$s#b#s#%j#3*#0Ds#Bs#As#?1H[S5D$s#Es#B#Cs#8#s#?s#>C#s#hs#A#$s#i#s#,j#.s#*#ZND)s#Js#G(CUS&S$XS-s#ms#F$#XS-s#Fs#E#s#@,s#o&ZS6D.s#Os#L-C&s#1%)$-#US'C4KCnJ$F$#$s#D$#%$#%##s#@3D3s#Ts#Q2Cs#G#UJF4S7CnJ$F$#$s#HG#%$#%##s#D4S8C$s#J$#nJ$F$#$S9C#%$#%##S:j#3(#,s#M&j#2F#U#Cj#2F#YS;F'#S<Cl#32.#]S=DAs#bs#_@Cs#U1#&s#D@<51#US(s#eUS>D&s#.s#-s#&%$#US.s#hUS?D&s#9s#8s#2%$#US)s#kUS@D&s#Fs#Es#?%$#UQH&Ls#is#P$#IWMs#pHC$s$5#s#(m#%#j#)E#YS/Es$8s$(s#{#\S0s#zs#ys#xs#xs$)s#|s#v#,s$:C\S0s$;s$;s$*s#}CC$#XOEEs$,CURIWS#H#C$s$?%#m#'#j#4s$A#YS/s$Bs$Bs$6s$4#j#5s$:#j#6SA#j#7s$E##"). Qed.
Lemma chain_slow_eq : forall fk sxs l,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  chain_slow (mkbc fk) sxs l = chainRo fk (map strip sxs) l.
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros l HF; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF]. cbn [chain_slow chainRo map]. rewrite (g1cB_eq _ _ H1). apply IH. exact HF.
Qed.
Scheme kc__11 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__12 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.pk_res Sort Prop.
Lemma chainK_eq : forall fk sxs K same_of br2,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  match kbase K with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK (mkbc fk) sxs K same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.stx); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_sp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_a); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_w); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kbase); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_bid); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.chainK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.chain_slow); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); (KReplay.sort_at constr:(@Stdlib.Lists.List.Forall_nil_iff) [0]); constr:(@kc__11); constr:(@Stdlib.Lists.List.Forall_cons_iff); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.g1cB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_v); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.pk_res); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1pc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.pk_list); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.obrB); constr:(@kc__10); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcK_eq); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB_eqf); constr:(@kc__12); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.PKeep); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.PRepl); constr:(@Corelib.Init.Datatypes.app); constr:(@Stdlib.Lists.List.app_nil_r)|] [|@x; @sx; @kb; @br2; @same_of; @K; @sxs; @HK; @HS; @l; @a; @P; @A; @hints; @wv; @w; @wa; @sp; @p; @HB; @o; @HK1; @H; @e; @E; @_H; @Hbr; @H1; @IH; @rest; @fk|] "#*^#E$'#J###M#$#0#\#2#%#1#&#.#-#/#4#=#,#7#I#N#'#(#+#S#3#;#5#*#E#:#8#6#<#>#9#@#)#o#?#A#B#P#b#h#s#x#C#z#y#w#|$$#L#j#l#r#q#p#D#{#}$#$%$&#~$'$(#K#R#Q#u#V#^#X#_#a#e#T#[#`#d#t#W#U#n#m#v#k#]#c#i#H#Y#Z#O#f#gC#f&#g&#h&#i$#j%#k$#l%#m%#n&#o$#p$#q$#r&#s%#t$#u'#v$#w+#x%#N+#y)#z$#{(#|(#}$#T+#~$$#$$$%$%$$&%#$(;S$;Ck#$SFE?S;S;US%#,D&S6(D1#=$-D>#2(&%##S)*#j#%C#$C#L8L&S-)#D#1J#.DUS&#*F0#E$#j#%C#$C#S'')#US<:#:F#nS%$H$#$S./#%$#&%##9/S'S&LJ@S$+S$S&#/2S'##s#$&#k##(#k##7#k#'s###k#(s#&#k#)S$#j#*s#)#&S'2#s#$s##A#S)s#(#j#%C#@C$C$#)s#+D#s#.J#$C;&'$#nS%$H$#$S.s#%#%$#&##9/s#0)6As#7#j#+%#j#,+#j#'s#6#j#(s#9#j#)S$#2s#,s#5s#4s#2#S)s#9#j#%C#$C#L&S()#D#s#?J#'#s#+nS%$H$#$S.s#5#%$#&##s#)9'S'S&LJ/(S's#'#s#H$#k##&#k##,#k#'s#G#k#(s#J#k#)S$#2/s#Fs#Es#C#S)s#J#j#%C#+CS'S&$C$#&R)#D#s#QJ#+CS-S6$Cs#?#'%#nS%$H$#$S.s#I#%$#&##s#=k##DS.;J+LFD$LJ#ULJ$S&LF'$#k##&#UJF$LJD'$#+S&JF$S&L#k##%#')#US&L$S'S&J'$#k##(#j##'#+S'LJ$S'S&#k##2#j###Fj##3#XSGLJFD:5/)$#j#-<#j#.F#j#/?#j#0S=#k#-@:k#.F#k#/s###k#0S=#&M2#s#vs#us#s#S)s#z#j#%C#BC#S(S-J,S(&N(S(1#=$-S(>#2(&%##S)*#$C-S-'$#,R(R1#=$-R>#28&%##S))#&O2#s$2s$1s$/#S)s$6#j#%C#$C#S('(#+CNR9)#S-S6S'+S$S-s#~/+%##s$C%#j##(#&G2#s$>s$=s$;#S)s$B#j#%C#$C#R,M(M1#=$-M>#2-&%##S))#&I2#s$Ks$Js$H#S)s$O#j#%C#$C#MWSH'GN&S*,K(K-K3K.KUN#4)('&%M#R9*GMNR&P/#KDnS7#$#$s$c&#%#%$#-#/.GD#s$e$#j#-s$f#;E;SI?s$i#?#%k#'s$g#k#1'#k#)S$#k#2H#k#3SJ#k#4SK#k#5S)#US>I0M6@E5?M[D?>=<M$#%02#%s$x2##s$y(#j#6+#8NUS%HA#D8M#%#D8G#'#D&S#)#D#s%$G#UIs$q#E#s$pj#%C#+CS,P$C$#'(##s%+Os$pnS%$H$#$S.F#%$#&$##,S,(S,-S,3S,.S,UK#43('&%I#G0I#55I6S#+*)(Is#$#%s#0s#2#%s%<s#2##s%='#k#+0#k#7<#j#8B#8KVS?HD#s#%$#)@F#s%AG#*Js%>#E@#j#%C#$C#?''#&S0)#J#s%IK#US*s%:*Ls%G#E$#j#%C#+CS1S,$C$#')#&S4,S#(S#-S#3S#.S#US*#4)('&%P#I0P#5+P6S4+*)(Ps#I#%s#Us#W#%s%as#W##s%b'#j##1#UPs%P*S&s%]#E$#j#%C#+CS#S1$C$#&S/)#S&#s%hS*#&S+)#S'US#s%[*S-s%h#E$#j#%C#+CS/S4$C$#&Q,S+(S+-S+3S+.S+US##4)('&%S0#F0S0#5+S06Q+*)(S0s#i#%s#us#w#%s&%s#w##s&&'#k##1#j#'s&$#US1s%q*S6s%~#E$#j#%C#+CS4S0$C$#US0s%w*S(s&(#E$#j#%C#BC#S+S/F1;*S-##E9#$C'S/'$#.S2US0#(S21#*S(##E&#US4s&+*Rs&8#E$#j#%C#$C#S+'(#&S8,Q(Q-Q3Q.QUS4#))R4*)('&S/$#0S/#5,S/6S8,+*)S/s$:#%s$Fs$H#%s&Rs$H##s&S'#j##2#US/s&A*Ns&N#E$#j#%C#$C#S2.S3US/#(S31#*N##E&#US2s&L*Os&Y#E$#j#%C#$C#S3VS?HO&S@,S9(S9-S93S9.S9UQ#))G4*)('&S3$#0S3#&SL)#DnS%$H$#$s&nD#%$#&##s&W6S@.-,+S3s$]#%s$is$k#%s&us$k##s&v)#j#8s$Y#,S5(S5-S53S5&S:)#O.S5US2#.S:US3#(S:1#*D##E&#nS%$H$#$S.D#%$#&##SAj#8s$i#8Q7s$ks#&$F#M]SBS:4321Q/-#7s$ms#(6#%M426543Q/10Q#54Q6S:9876Qs$y#%s%)s%+#%s'5s%+##s'6'#m#*#j#+s#2#j#9s#8#V#FDj##s#@#j##s#\#:s#]s#Xs#G#Dl#+s#is#d#l#:s&%s%}#j#+s#p#7s'=s$1s#w#PDj#:s$4#V#FDj##s$9#j##s$V#:s$Ws$Qs$A#Dj#+s$[#j#7s$c#j#&H#U#Dj#;H#8OUS<H#s%0$##s'KMs'4)s$cDnS%$H$#$s'MD#%$#&##s'66S#s%#s$~s$}s$|Is%<#%s%Hs%J#%s'Ts%J##s'Us${#j#8s%8#4s%3s%(s%'s%&s%%Is%#D0I#6S#s%*s%)s%(s%'Is%Cs'>%s%Os%Q#%s'[s%Q##s'\&#j#'s'Y#,P(P-P3P.PUG#.S1UI#(S11#*D##E&#nS%$H$#$S.D#%$#&##SAj#8s%M#7s%NA#SMs%-F]SBS110/.Ks'R,#7s'js'S3#OD7s%Qs#$;#s%0F&S14#5432K0O0K#5%K6S18765Ks%^#%s%js%l#%s'vs%l##s'w'#m#+#j#+s#,#j#7s#.#YSCHs%=s#2#FV#DS(l#7s%^s%\#l#8s%as%`#USDs&/USNI7s%ns%ms%e%$#,G(G-G3G.GUR#4s&8('&%N#S(0N#5s&:N<s&;+*)(Ns%u#%s&%s&'#%s(1s&'##s(2'#0GD&S,,S*(S*-S*3S*5'G<('&%$Gs&$#%s&0s&2#%s(<s&2##s(=,#9s#,S*KGO/s%wPDnS7#$#$s(@F#%#$$#-#<s#/s#As#@s#?s#>Ks&+s#,%s&7s&9#%s(Cs&9#/s#2S*##s(E'#k#<+#j#6S7#0OSO,I(I-I3I5s&JO<s&K'&%$Os&8#%s&Ds&F#%s(Ps&F##s(Q+#+S$Gs(3/s#AS*D#s(T8#j#-s(U##s(RKs#d#Es%gs(Aj#%C#$C#s%e'&##s(WGs(@nS%$H$#$S.D#%$#&$##)s%fD#s(ZI##Es%Ys(Ij#%C#$C#S1'&##s(_Ks(HnS%$H$#$S.F#%$#&$##k#++#j#8s&H#)s%pF#s(dI##Es%cs&%j#%C#$C#s%a'&#)s%aJ#s(jS*#US,s([#E#s&#j#%C#$C#S#''#j##*#+CS0S#$C'#)s%hL#s(tP#*S's(q#Es%i#j#%C#$C#s%g#Es%@s%kj#%C#BC#S2S+F*S6s%F#Es%I#$C&S+'$#1s%?*S-##Es%=##Es%4s%Yj#%C#$C#S2'&#&S5)#S(#s)-S4#US+s(z#E#s%Qj#%C#$C#Q''#j##+#.S8US+#(S81#*R##E&#UQs)**Ms)7#E$#j#%C#$C#S8)s%;M#s)@S2#US3s)1#E#s%Cj#%C#$C#S5XSP'#S-Dj#+*#j#=0#V#FDj##:#j##s#&#:s#'s#$:#Dl#+s#/s#+#l#:s(7s(3#j#+s#4#j#>s#9#V#FDj##s#=#j##s#L#:s#Ms#Js#A#Dj#+s#\#j#&H#U#Dj#;H#j#+s'/DYSCHs#U$#DU#Nl#8s'=s'A#YKGOML#ZSEs)as#ms#j#s$'Dj#<s#o#USQD0K##s)e#s$$/s&yS,J/s&zS,D#s)h$#j#-s)i#/s'FPFAs)k#<s'Hs'=s'<s';s':Is'Vs'5%s'bs'd#%s)ns'd#ZSEs)oF(&#Dj#<-#j#-s)q#U#Dj#-s)s#XSRs$/4#DU#Fl#6s'uS7#l#<s$Ts$G#9s((ONRS(nS7#$#$s)ys$O#%##$#-s's/s(*Os(%#s){$#m#'#WSSS$s((s)^VSTS$s()7s*#s(*s'w%$#+CGO9s(1#NRS(+S$Ns)c/s(3%##s*(%#m#(#j#,s(2#j#?s(8#V#FDj##s(B#j##s(T#:s(Us(Ps(I#Dl#,s(is(^#l#:s(ss(o#j#+s)7#j#,s)?#j#'s*0#j#(s*3#j#)S$#j#@s)H#j#As*7#j#%C#YSUCs)ns)\#Dj#*s*:#j#Bs*<##"). Qed.

Lemma flat_map_flat_map : forall (A B C : Type) (f : A -> list B) (g : B -> list C) l,
  flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof. intros. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite flat_map_app', IH. reflexivity. Qed.
Lemma chain_slow_flat_map : forall bc sxs l, chain_slow bc sxs l = flat_map (fun K => chain_slow bc sxs [K]) l.
Proof.
  intros bc sxs. induction sxs as [|sx rest IH]; intros l.
  - cbn. induction l as [|x r IHl]; [reflexivity|]. cbn. rewrite <- IHl. reflexivity.
  - cbn [chain_slow]. rewrite IH. rewrite flat_map_flat_map.
    f_equal. apply functional_extensionality. intros K. cbn [flat_map]. rewrite app_nil_r. rewrite <- IH. reflexivity.
Qed.
Lemma chainK2_eq : forall fk sxs K okb same_of br2,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  okb = kbase K ->
  match okb with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK2 (mkbc fk) sxs K okb same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.stx); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_sp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_a); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.a_off); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.elen); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_w); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kbase); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_bid); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.chainK2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.chain_slow); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); (KReplay.sort_at constr:(@Stdlib.Lists.List.Forall_nil_iff) [0]); constr:(@kc__11); constr:(@Stdlib.Lists.List.Forall_cons_iff); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.g1cB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.sx_v); constr:(@Stdlib.Lists.List.flat_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.pk_res); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.prune1pc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.pk_list); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.obrB); constr:(@Corelib.Init.Logic.eq_ind); constr:(@kc__10); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcK_eq); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.prune1pcB_eqf); constr:(@kc__12); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.PKeep); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.PRepl); constr:(@stdpp.tactics.f_equal_help); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@kc__7); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.p_expr_eqb_eq); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.chain_slow_flat_map); constr:(@Corelib.Init.Datatypes.app); constr:(@Stdlib.Lists.List.app_nil_r)|] [|@x; @sx; @okb; @kb; @br2; @same_of; @K; @sxs; @HK; @Hokb; @HS; @l; @a; @P; @A; @kb'; @K'; @hints; @wv; @w; @wa; @sp; @p; @o; @HK1; @H; @e; @E; @_H; @Hbr; @HB'; @EQ; @b; @H1; @IH; @rest; @fk|] "#-d#S$;#X###]#W#[#$#2#Z#'#&#/#4#.#0#(#1#5#%#-#3#7#6#,#8#:#*#=#;#b#9#<#S#@#+#)#?#>#B#A#F#~#G#K#}#I#J#L#E#C#D#H#N#_#p#v$&$.$-$0$4#O#y$6#\#x#z$%$$$#$/$1$3$5$9$:$;#R$<$8$7$=$2$>$?#Y#a#`#o#e#r#m#l#s$(#g#n#q#k#f#c#j#d$'#|#u#w#{$,$)#V$*#h#i$+#^#tG#x&#y&#z%#{$#|&#}%#~%$#&$$&$%$$&$$')$($$)$$*$$+$$,'$-%$.$$/%$0($1+#N'#Z+$2%$3%$4$$5)#`)#]+$6$$7$#$($8($9%$:$=F=CUJGk#$SREESGSGUJ#1D&S,,D0#A$2DB#3(&%##S/*#j#%C#$C#K/K#2L#&S)(#D#2L#-DUQ#%H1#E$#j#%C#$C#S,))#USH;#;S$#nJ$G$#&S2K#%$#'%##./S,S5QKLFF*FS5#'2S,##s#&&#k##(#k##6#k##9#k#(s#%#k#)s#(#k#&s#*#k#*F#j#+s#-#&S53#s#'s#&s#$#S/s#+#j#%C#FC$C$#&S4(#D#s#2L#$C>')$#nJ$G$#&S2K#%$#'##<'(*96s#<#j#,%#j#-s#,#j#.-#j#(s#;#j#)s#>#j#&s#@#j#*F#31s#;s#:s#8#S/s#?#j#%C#$C#K&S%(#D#s#EL#)#s#0nJ$G$#&S2K#%$#'##s#..'S,S5QKL'(S,s#,#s#O$#k##&#k##s#?#k##-#k#(s#N#k#)s#Q#k#&s#S#k#*F#3s#Ds#Ns#Ms#K#S/s#R#j#%C#*CS5Q$C$#&O(#D#s#YL#*CS)S4$Cs#F#)%#nJ$G$#&S2K#%$#'##s#Dk##DS2=S$*LHD$LS$#ULS$$KLH)$#k##&#US$H$LS$D)$#*KS$H$KL#k##%#))#UKL$QKS$)$#k##(#j##'#*QLS$$QK#k##2#j###Hj##3#XSSLS$HD75/)$#j#/<#j#0H#j#1?#j#2SI#k#/@:k#0H#k#1s###k#2SI#&P3#s#~s#}s#{#S/s$&#j#%C#CC#S%S)L1S%&M,S%0#A$2S%B#3(&%##S/*#$C-S))$#1O,O0#A$2OB#38&%##S/)#&R3#s$:s$9s$7#S/s$>#j#%C#$C#S%)(#*CMO.)#S)S4S,S5*FS)s$)'+%##s$L%#j##(#&I3#s$Fs$Es$C#S/s$J#j#%C#$C#O1P,P0#A$2PB#3-&%##S/)#&N3#s$Ss$Rs$P#S/s$W#j#%C#$C#PWST'IM&S#1S&,S&2S&5S&-S&UO#8)('&%P#S%.*IPMOS%/D%DS$&S0.#S(HS&IR*FHs$M'%S(#nE#$##s$p'#%#%##&S**FDs$Q'$S##nJ$G$#$s$t,#%$#3&##j#4F#9FF#H&S('#S&DnJ$G$#&s$yP#%$#'%##nS;#$#$s$z4#%#3$#/#'<ID#s$|$#j#/s$}#=E=SUEs%$#E#%k#(s$}#k#5'#k#*F#k#6G#k#7SV#k#8SW#k#9S/#USJN4Ps#$FE<s#-P[Ds#-s#,s#+s#*P$#+02#+s%32##s%4(#j#:+#(=DnJ$G$#$s%2D#%$#'##s$v:S#s#4s#3s#2s#1P+#+79#+s%:9##s%;/#j#;s%:#/P#s%<D#&S'(#D#s%<M#URs%,#E#s%+j#%C#*CS#N$C$#)(##s%COs%+nJ$G$#&S2H#%$#'$##1S#,S#2S#5S#-S#UP#83('&%I#M4I#(s#?DnJ$G$#$s%NS$#%$#'##s%6:S',+*)Is#'#+s#3s#5#+s%Vs#5##s%W(#k#,1#k#-=#j#;s%X#;GD/R#s%[$#(AH#s%ZM#%S$s%W#EA#j#%C#$C#@)'#(s#RS$#s%aP#UIs%Q%Ls%_#E$#j#%C#*CS(S#$C$#))#1S',S'2S'5S'-S'UI#8s#f('&%N#R4N#(s#hL:S0+*)(Ns#J#+s#Vs#X#+s%ys#X##s%z'#j##0#US&s%f%Ks%t#E$#j#%C#*CS'S($C$#&S+(#K#s&#I#&S.(#QUS(s%q%S,s&##E$#j#%C#*CS+S0$C$#&S-1S.,S.2S.5S.-S.US(#8)('&%S*#H4S*#(+S,:S-+*)(S*s#j#+s#vs#x#+s&=s#x##s&>'#k##1#j#(s&;#US#s&+%S5s&9#E$#j#%C#*CS0S*$C$#US's&1%S4s&?#E$#j#%C#CC#S.S+H0;%S,##E9#$C'S+)$#-S1US'#,S10#%S4##E&#US*s&A%S)s&O#E$#j#%C#$C#S.)(#&S61S-,S-2S-5S--S-US*#()S)8*)('&S+$#4S+#:S6+*)(S+s$:%+s$Fs$H#+s&is$H##s&j&#j##1#US0s&V%S%s&d#E$#j#%C#$C#S1-S7US0#,S70#%S%##E&#US.s&a%Ms&o#E$#j#%C#$C#S71S3,S32S35S3&S8(#M-S3US.#;GM-S8US-#,S80#%D##E&#nJ$G$#$S2D#%$#'##SKj#;s'.#/S->s'0,$H#O]SLS85432S-0.#j#,7#j#<=#V#HDj##s#%#j##s#@#7s#As#<s#,#Dl#,s#Ms#H#l#=s%ts%p#j#,s#T#?s'8s#qs#[#S&Dj#=s#t#V#HDj##s#y#j##s$9#7s$:s$4s$%#Dj#,s$=#j#-s$E#j#'G#U#Dj#>G#USHG/M#s'H$##s'FS%s'.8s$ks$`s$_s$^s$]Is$[D4I#:S's$bs$as$`s$_Is$}s'1+s%-s%/#+s'Ps%/##s'Q&#j#(s'M#1N,N2N5N-NUM#-S(UR#,S(0#%D##E&#nJ$G$#$S2D#%$#'##SKj#;s'^#>s'_;#SXs$cH]SLS(10/.Rs'E,#?s'^s'F3#ODj#,;#j#-=#DGs$jA#OV#S,S5>s'fOs%.#AS,1I,I2I5I-IUS%#8s%r('&%M#S)4M#<s%tM:N+*)(Ms%E#+s%Qs%S#+s'ts%S##s'u'#m#0#USMs%zUSYN?s%Os%Ns%F%$#@s%}3210Ms%M++s%Ys%[#+s'|s%[##s'}/#4ID<s%BI@s%Cs%8s%7s%6s%5Is%S#+s%_s%a#+s(&s%a##s(''#.s%qS#S&IRP&S1.#S0HS(S#N'$S0s%wnE#$##s(,s%{#%#$##'s$bS*s%unJ$G$#$s(.s%~#%$#3$##j#4F#9FF#H's&#S(DnJ$G$#&s(2S&#%$#'$##nS;#$#$s(3H#%#-$#/#1S(2S(5S(<s&$S&@s&%&s#;%$S&s%g#+s%ss%u#+s(:s%u#'s&(S###s(<+#k#?8#j#:S;#4RSZ<s&'R@s&(s#Ls#Ks#Js#IRs%p#+s%|s%~#+s(Cs%~##s(D'#*FIs($'s&3S#D#s(GA#j#/s(H#/S&#s(HD#(s%'D#s(GI#UNs(7#E#s(6j#%C#*CS*S'$C$#)(##s(NRs(6nJ$G$#&S2H#%$#'$##(s%.D#s(QS&##Es$ts(?j#%C#$C#S*)&##s(VIs(>nJ$G$#&S2S$#%$#'$##k#,+#k#-6#j#;s(]#/N#s(_s%d#(s%>H#s(^I##E9s%bj#%C#$C#8)&#(s%AS$#s(dS&##Es%+s%`j#%C#$C#s%))&#(s#GL#s(jN##Es%Gs%Qj#%C#$C#S0)&#j##)#$C&s%H(s%GK#s(rS###Es%#s%8j#%C#*CS1S.$C$#US+s(f#E#s%7j#%C#CC#S7S-H%S,s$j#Es$m#$C&S-)$#-S6US+#,S60#%S4##E&##Es$qs%4j#%C#$C#S7)&#(s$lS)#s).S+#US1s(z#E#s%&j#%C#$C#S6)'#j##*#-S9US1#,S90#%S%##E&#US7s)*#E#s%'j#%C#$C#S9&SB(#M#s)AS-#US6s)1%Ps)?#E$#j#%C#$C#S8XSN(#S,Dj#,,#j#@1#V#HDj##;#j##s#&#7s#'s#$;#Dl#,s#2s#.#l#=s(1s(-#j#,s#8#j#As#=#V#HDj##s#A#j##s#N#7s#Os#Ls#D#Dj#,s#R#j#-s#Y#j#'G#U#Dj#>G#/I#s)_s$w##s)]Ps)Ej#,#Dj#-%#DGs#d(#RV#S%S)[S&IRPMLS%#>s)hs$%s#~#s$DDj#?s$'#US[D4S&##s)l#s$4.s&>S+HS'S(S#'s&?S+s'^nE#$##s)os'b#%#$##'s$IS0s'\nJ$G$#$s)qs'e#%$#3$##j#4F#9FF#L's&PS'S$nJ$G$#&s)uN#%$#'$##'s&RS'D#s)w$#j#/s)x#/S##s)xD#(s$TD#s)wN##Es&Ts)ej#%C#$C#s&R)&##s)|S&s)dnJ$G$#&S2H#%$#'$##.s&(S1HQS*S''s&)S1s'tnE#$##s*)s'x#%#$##&S7'#S.s'snJ$G$#$s*,s'|#%$#3%##j#4F#9FF#Q's$dS0KnJ$G$#&s*0S$#%$#'$###s*1#$k#,.#k#-7#j#;s*2#/S(#s*4s'9#(s$lH#s*3N##Es&ls'7j#%C#$C#s&j)&#j#*F49FF#Q%DQ&S3;GQ.$S-H#S0S*'%S-s(3nE#$##s*D'#%#$##'s&FS1s(1nJ$G$#$s*Fs(:#%$#3$##j#4F#9FF#S5#s*I#Dj#/s*J#%DK;GK.s&NS1H#S*S'nE#$##s*N%#%###s#(nJ$G$#$s*Os(C#%$#3##s#&j#4F#WS>FF#WS>FF7k##Fs*Sk##s*Ts*TVS>FFk##%$6#$6s*VD/H#s*X#D/L#s*Z#D%DS4&SC;GS4.$S3Q#S1S.*FQs*@'&S3#nE#$##s*c(#%#%##*FKs*C's&CS6#nJ$G$#$s*fH#%$#3%###s*g#$k#B.#j#;s*g##s*hs*Ys'm%HS46ED%S$S)#E#D%KO#E#D&S<.#SDS)s&LS3S6'$SDs)+nE#$##s*tH#%#$###s*u#$k#C(#j#DE#%LS%#E#S\WS]KOD#GKO/S%#s*{#s($&S?;GR.$S:O#S8S9*FOs*`'&S:##s+'%#k#B)#j#3G#/S)#s+)#s&a;GPXS^s++/#D&SE(#P#s++S3#US8s*w%Rs+)#E$#j#%C#*CS:SB$C$#))#(8R#s+4S9#USCs+$%Is+2#E$#j#%C#$C#S:)(#j##+#*CS<S:$C'#&S@(#I#s+@S8#USBs+0%Ns+>#E$#j#%C#*CS?SE$C$#US<s+6%S(s+D#E$#j#%C#CC#S=S@H-S=US:#,S=0#%S###E&#$C*S@)$#-SAUS<#,SA0#%S(##E&#USEs+I%S's+W#E$#j#%C#$C#S=)(#&SO(#S'#s+bS<#US?s+R%S*s+`#E$#j#%C#$C#SA)(#j##,#-SFUS?#,SF0#%S*##E&#US=s+_%S+s+m#E$#j#%C#$C#SF&S_(#S+#s+wS@#USAs+g%S.s+u#E$#j#%C#$C#SOXSN(#S,Dj#,,#j#@2#V#HDj##<#j##s#+#7s#,s#'<#Dl#,s#;s#3#l#=s*gs*c#j#,s#B#j#As#I#V#HDj##s#N#j##s#a#7s#bs#\s#R#O[SDS%s#gS9S3S's#f#j#Bs#i#[SPGMs#l#QDKl#Cs#xs#w#j#Cs#z##Es#|S`&S:*FS4s+w'$SC#6s,>#j#C'#XSas$')#HU#Dl#Cs$4s$2#l#Ds$6E#j#Bs$8#j#3G#U#Dj#>G#/S$#s,G#s'_&S9*FLs,*'$S7#6s,M#j#B'#DGs$D*#HU#Dl#Bs$Ws$U#l#;s*Fs,P#j#4F#YSbFs,Ts$bs$u#\SQs$`s$_s$^s$^s$cs$vs$\#6s,VQ\SQs,Ws,Ws$ds$cQQ$#'s))S+QWScs)*S+Q?s,Zs$zs$n%$#j#,s$}#j#-s%(#j#'G#U#Dj#>G##s,^s'vs&^'s):S*L6s,b#j#,s&f#j#-&#DGs%3(#S&V#MO<s*YN@s*Zs)Xs)Ws)Vs)UNs*;#+s*Gs*I#+s,js*I#>s,kHs%Q'#Dj#?s%^#j#/s,m#U#Dj#/s,o#XSds'4s%e#DU#Hl#:s*hS;#l#?s'Xs'T#.s*wRMOS%S).s*bS#HIRP's*cS#s*fnE#$##s,ws*j#%#$##'s*;Ns*dnJ$G$#$s,ys*m#%$#3$##j#4F#9FF#HnJ$G$#&s,|M#%$#'##s*_nS;#$#$s,}s'l#%#+$#/#'s+%Rs*|#s-#$#m#/#WSeFs+#s,`VSfFs+$?s-'s+%s*d%$#*CIR.s+,#MOS%S)*FMs,e's+.%##s-,%#m#(#j#.s+-#j#Es+3#V#HDj##s+=#j##s+O#7s+Ps+Ks+D#Dl#.s+ds+Y#l#=s+ns+j#j#,s,2#j#-s-%#j#.s,;#j#(s-4#j#)s-7#j#&s-9#j#*F#j#Fs,E#j#Gs-=#j#%C#YSgCs,ps,[#Dj#+s-@#j#Hs-B##"). Qed.



Lemma SX_OK_mono : forall bc t t' sx,
  (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> SX_OK bc t sx -> SX_OK bc t' sx.
Proof. intros bc t t' sx Hm (H1 & H2 & H3). split; [apply Hm; exact H1|]. split; assumption. Qed.

Lemma mk_stxs_ok : forall fk log t sxs t',
  NTI (mkbc fk) t -> mk_stxs (mkbc fk) log t = (sxs, t') ->
  NTI (mkbc fk) t' /\ Forall (SX_OK (mkbc fk) t') sxs /\ map strip sxs = rev log
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
  intros fk log. induction log as [|[a w v] older IH]; intros t sxs t' HT H.
  - cbn in H. injection H as <- <-. split; [exact HT|]. split; [constructor|]. split; [reflexivity|]. intros; assumption.
  - cbn [mk_stxs] in H. destruct (mk_stxs (mkbc fk) older t) as [sxs0 t1] eqn:E0.
    destruct (intern (mkbc fk) t1 (a_base a)) as [[bid bi] t2] eqn:EI.
    injection H as <- <-.
    destruct (IH t sxs0 t1 HT E0) as (HT1 & HS & Hmap & Hm1).
    destruct (intern_ok _ _ _ _ _ _ HT1 EI) as (HT2 & -> & HIn & Hm2).
    split; [exact HT2|]. split.
    + apply Forall_app. split.
      * apply Forall_impl with (P := SX_OK (mkbc fk) t1); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm2.
      * constructor; [|constructor]. split; [exact HIn|]. split; reflexivity.
    + split; [rewrite map_app, Hmap; reflexivity|]. intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.

Lemma Forall_SX_sp : forall fk t sxs, Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs.
Proof. intros fk t sxs H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H]. intros sx (_ & _ & X). exact X. Qed.

Lemma Forall_SX_same : forall fk t sxs kb bid,
  NTI (mkbc fk) t -> In (kb, bid) (nt_bucket t (bkey kb)) -> Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => Pos.eqb bid (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs.
Proof.
  intros fk t sxs kb bid HT HIn H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H].
  intros sx (H1 & _ & _). exact (nt_same_eq _ _ _ _ _ _ HT HIn H1).
Qed.

Lemma entriesV_eq : forall fk sxs kn t,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  entriesV (mkbc fk) sxs kn t = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs kn. induction kn as [|K rest IH]; intros t HT HS.
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesV]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app.
    destruct (kbase K) as [kb|] eqn:HB.
    + destruct (intern (mkbc fk) t kb) as [[bid bi] t'] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT' & -> & HIn & Hm).
      assert (HS' : Forall (SX_OK (mkbc fk) t') sxs).
      { apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm. }
      rewrite (IH t' HT' HS'). f_equal.
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
      cbn [bi_br]. split; [reflexivity|]. exact (Forall_SX_same _ _ _ _ _ HT' HIn HS').
    + rewrite (IH t HT HS). f_equal.
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
      reflexivity.
Qed.

Lemma stores_part_eq : forall fk t sxs,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  stores_part (mkbc fk) sxs = SPRo fk (map strip sxs).
Proof.
  intros fk t sxs HT. induction sxs as [|sx newer IH]; intros HS; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [stores_part SPRo map]. rewrite (IH HS). f_equal.
  destruct H1 as (HIn & Hbr & _). destruct (sx_a sx) as [b o] eqn:Ea. cbn [a_base a_off] in HIn, Hbr.
  rewrite chainK2_eq; [unfold kw, strip; rewrite Ea; apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | reflexivity |].
  cbn [a_base]. split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS).
Qed.

Lemma carryK0_eq : forall log kn hints,
  carryK0 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK0. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical. unfold carryV.
  destruct (mk_stxs (mkbc (facts_of kn)) (s :: older) nt_empty) as [sxs t] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT & HS & Hmap & _).
  rewrite (stores_part_eq _ _ _ HT HS), (entriesV_eq _ _ _ _ HT HS), Hmap. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint pt_map {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
  match t with
  | PTLeaf => PTLeaf
  | PTNode l o r => PTNode (pt_map f l) (match o with Some a => Some (f a) | None => None end) (pt_map f r)
  end.
Lemma pt_get_map : forall (A B : Type) (f : A -> B) t k,
  pt_get (pt_map f t) k = match pt_get t k with Some a => Some (f a) | None => None end.
Proof. intros A B f t. induction t as [|l IHl o r IHr]; intros k; [destruct k; reflexivity|]. destruct k; cbn; auto. Qed.

(* [comment removed for export] *)
Definition kdescr (K : kentry) : option (expr * Z * option Z) :=
  match K with
  | KWord (SA kb kk) w _ => Some (kb, kk, Some (zlit64 (Z.of_nat w)))
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      Some (kb, kk, match len with ELit z => Some (zlit64 z) | _ => None end)
  | KImg lo hi => Some (ELit 0%Z, lo, if Z.ltb (hi - lo) (2 ^ 64) then Some (zlit64 (hi - lo)) else None)
  | _ => None
  end.
Record einfo := EI { ei_bid : positive; ei_gid : positive; ei_kb : expr; ei_br : option (Z * Z); ei_k : Z; ei_m : option Z }.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gval : Type := (positive * expr * option (Z * Z) * (Z * Z))%type.
Definition gtab := ptree gval.
Record gst := GST { gs_gid : ptree (ptree positive); gs_next : positive; gs_bnds : gtab }.
Definition gst_empty : gst := GST PTLeaf xH PTLeaf.
Definition gkey (kk : Z) : positive :=
  let g := Z.shiftr kk 8 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.   (* [comment removed for export] *)
Definition ggroup (gs : gst) (bid : positive) (kk : Z) : positive * gst :=
  let gk := gkey kk in
  let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
  match pt_get inner gk with
  | Some gid => (gid, gs)
  | None => let gid := gs_next gs in
            (gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
  end.
Definition bnd_add (gs : gst) (gid bid : positive) (kb : expr) (obr : option (Z * Z)) (lo hi : Z) : gst :=
  GST (gs_gid gs) (gs_next gs)
      (match pt_get (gs_bnds gs) gid with
       | Some (b, kb0, o, (l, h)) => pt_set gid (b, kb0, o, (Z.min l lo, Z.max h hi)) (gs_bnds gs)
       | None => pt_set gid (bid, kb, obr, (lo, hi)) (gs_bnds gs)
       end).
Fixpoint scan_entries (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfo) * ntab * gst :=
  match kn with
  | [] => ([], t, gs)
  | K :: rest =>
      match kdescr K with
      | Some (kb, kk, om) =>
          let '(r, t1) := intern bc t kb in
          let '(bid, bi) := r in
          let '(gid, gs1) := match om with
                             | Some m => let '(gid, gs0) := ggroup gs bid kk in (gid, bnd_add gs0 gid bid kb (bi_br bi) kk (kk + m)%Z)
                             | None => (xH, gs)
                             end in
          let '(infos, t2, gs2) := scan_entries bc rest t1 gs1 in
          (Some (EI bid gid kb (bi_br bi) kk om) :: infos, t2, gs2)
      | None =>
          let '(infos, t2, gs2) := scan_entries bc rest t gs in
          (None :: infos, t2, gs2)
      end
  end.

Definition sx_m1 (sx : stx) : Z := zlit64 (Z.of_nat (sx_w sx)).
(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition hull_in_side (kb : expr) (obr : option (Z * Z)) (glo ghi : Z) (cm : saddr * expr) : bool :=
  match snd cm with
  | ELit ml0 =>
      let c := fst cm in let ml := zlit64 ml0 in
      if (expr_eqb kb (a_base c) && Z.leb (a_off c) glo && Z.leb ghi (a_off c + ml))%lzb then true
      else match a_base c, obr with
           | ELit zc, Some (lo1, hi1) =>
               let vc := zlit64 zc in
               (Z.leb (vc + a_off c) (lo1 + glo) && Z.leb (hi1 + ghi) (vc + a_off c + ml))%lzb
           | _, _ => false
           end
  | _ => false
  end.
Local Close Scope lzb_scope.
(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition verdict (sx : stx) (g : gval) : bool :=
  match g with
  | (b, kb, obr, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx)
      then (* [comment removed for export] *)
           (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo || Z.leb ghi (a_off (sx_a sx)))%lzb
      else
      if (match sp_rng (sx_sp sx), obr with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo || Z.leb ghi (lo1 + a_off (sx_a sx) - hi2))%lzb
          | _, _ => false
          end) then true
      else existsb (hull_in_side kb obr glo ghi) (sp_D (sx_sp sx))
  end.
Local Close Scope lzb_scope.
(* [comment removed for export] *)
Fixpoint mk_fl (g : gval) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict sx g then mk_fl g rest else (sx, rest) :: mk_fl g rest
  end.
Definition gfl : Type := (gval * list (stx * list stx))%type.
Definition mk_gl (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl g sxs)) bnds.

Local Open Scope lzb_scope.
Definition obr_eqb (a b : option (Z * Z)) : bool :=
  match a, b with
  | Some (x1, y1), Some (x2, y2) => Z.eqb x1 x2 && Z.eqb y1 y2
  | None, None => true
  | _, _ => false
  end%lzb.
Local Close Scope lzb_scope.
(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition inb (g : gval) (ei : einfo) : bool :=
  match ei_m ei, g with
  | Some m, (b, kb, obr, (lo, hi)) =>
      Pos.eqb b (ei_bid ei) && expr_eqb kb (ei_kb ei) && obr_eqb obr (ei_br ei) && Z.leb lo (ei_k ei) && Z.leb (ei_k ei + m) hi
  | _, _ => false
  end%lzb.
Local Close Scope lzb_scope.

Fixpoint chainKF (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainKF bc fl' K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition knormal (K : kentry) : bool :=
  match K with
  | KWord _ w _ => Z.ltb (Z.of_nat w) two64
  | KZero _ (ELit z) | KUnk _ (ELit z) | KFill _ (ELit z) _ | KBlob _ (ELit z) _ => (Z.ltb 0 z && Z.ltb z two64)%lzb
  | _ => false
  end.
Local Close Scope lzb_scope.

Fixpoint entriesG (bc : bctx) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if (if inb g ei then knormal K else false) then chainKF bc fl K okb same_of br2 else chainK2 bc sxs K okb same_of br2
           | None => chainK2 bc sxs K okb same_of br2
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG bc sxs gl rest irest
  | _, _ => []
  end.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG bc sxs (mk_gl (gs_bnds gs) sxs) kn infos.

(* [comment removed for export] *)
Lemma zlit64_idem : forall z, zlit64 (zlit64 z) = zlit64 z.
Proof.
  intros z. unfold zlit64. change (if Z.leb 0 z then Z.ltb z two64 else false) with (Z.leb 0 z && Z.ltb z two64)%bool in *; destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [rewrite E; reflexivity|].
  pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as B.
  change (if Z.leb 0 (z mod two64) then Z.ltb (z mod two64) two64 else false) with (Z.leb 0 (z mod two64) && Z.ltb (z mod two64) two64)%bool in *; replace (Z.leb 0 (z mod two64) && Z.ltb (z mod two64) two64)%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.
Lemma zlit64_bounds : forall z, (0 <= zlit64 z < two64)%Z.
Proof.
  intros z. unfold zlit64. change (if Z.leb 0 z then Z.ltb z two64 else false) with (Z.leb 0 z && Z.ltb z two64)%bool in *; destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E.
  - apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - apply Z.mod_pos_bound. unfold two64. lia.
Qed.

(* [comment removed for export] *)
Lemma hull_in_side_member : forall bc kb obr glo ghi cm kk mm,
  hull_in_side kb obr glo ghi cm = true ->
  base_rangeB bc kb = obr -> (glo <= kk)%Z -> (kk + mm <= ghi)%Z -> (0 <= mm < two64)%Z ->
  sub_itvB bc kb kk mm (fst cm) (snd cm) = true.
Proof.
  intros bc kb obr glo ghi [c m] kk mm H Hbr Hlo Hhi Hmm. unfold hull_in_side in H. cbn [fst snd] in *.
  destruct m as [ml0| | | | | | |]; try discriminate.
  unfold sub_itvB. cbn [xloB].
  change (if (if expr_eqb kb (a_base c) then Z.leb (a_off c) glo else false) then Z.leb ghi (a_off c + zlit64 ml0) else false) with (expr_eqb kb (a_base c) && Z.leb (a_off c) glo && Z.leb ghi (a_off c + zlit64 ml0))%bool in *; destruct (expr_eqb kb (a_base c) && Z.leb (a_off c) glo && Z.leb ghi (a_off c + zlit64 ml0))%bool eqn:E1.
  - apply andb_prop in E1 as [E1 E3]. apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E2. apply Z.leb_le in E3.
    rewrite E1. replace (Z.leb (a_off c) kk) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    replace (Z.leb (kk + mm) (a_off c + zlit64 ml0)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - destruct (a_base c) as [zc| | | | | | |] eqn:Ec; try discriminate.
    destruct obr as [[lo1 hi1]|]; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
    change (if Z.leb 0 mm then Z.ltb mm two64 else false) with (Z.leb 0 mm && Z.ltb mm two64)%bool in *; replace (Z.leb 0 mm && Z.ltb mm two64)%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    unfold xinsideB. cbn [shares_var novars].
    unfold xinside_numB. cbn [xloB xhiB]. rewrite Z.eqb_refl. rewrite Hbr.
    replace (zlit64 mm) with mm by (unfold zlit64; change (if Z.leb 0 mm then Z.ltb mm two64 else false) with (Z.leb 0 mm && Z.ltb mm two64)%bool in *; replace (Z.leb 0 mm && Z.ltb mm two64)%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia); reflexivity).
    change (if Z.leb (zlit64 zc + a_off c) (lo1 + kk) then Z.leb (hi1 + kk + mm) (zlit64 zc + a_off c + zlit64 ml0) else false) with (Z.leb (zlit64 zc + a_off c) (lo1 + kk) && Z.leb (hi1 + kk + mm) (zlit64 zc + a_off c + zlit64 ml0))%bool in *; replace (Z.leb (zlit64 zc + a_off c) (lo1 + kk) && Z.leb (hi1 + kk + mm) (zlit64 zc + a_off c + zlit64 ml0))%bool with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma in_sidesB_of_hull : forall bc D kb obr glo ghi kk mm,
  existsb (hull_in_side kb obr glo ghi) D = true ->
  base_rangeB bc kb = obr -> (glo <= kk)%Z -> (kk + mm <= ghi)%Z -> (0 <= mm < two64)%Z ->
  in_sidesB bc D kb kk mm = true.
Proof.
  intros bc D kb obr glo ghi kk mm H Hbr Hlo Hhi Hmm. induction D as [|[c m] r IH]; [discriminate|].
  cbn [existsb] in H. cbn [in_sidesB].
  destruct (hull_in_side kb obr glo ghi (c, m)) eqn:E.
  - pose proof (hull_in_side_member bc kb obr glo ghi (c, m) kk mm E Hbr Hlo Hhi Hmm) as HM. cbn [fst snd] in HM. rewrite HM. reflexivity.
  - cbn [orb] in H. rewrite (IH H). destruct (sub_itvB bc kb kk mm c m); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ranges_apart_pcB_sides : forall bc sp b1 k1 z1 br2 b2 k2 z2,
  in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2) = true ->
  ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 (ELit z2) = true.
Proof.
  intros bc sp b1 k1 z1 br2 b2 k2 z2 H. unfold ranges_apart_pcB. rewrite H.
  match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.
Lemma ranges_apart_pB_sides : forall bc sp b1 k1 z1 b2 k2 z2,
  in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2) = true ->
  ranges_apart_pB bc sp b1 k1 (ELit z1) b2 k2 (ELit z2) = true.
Proof.
  intros bc sp b1 k1 z1 b2 k2 z2 H. unfold ranges_apart_pB. rewrite H.
  match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.

Lemma kdescr_kbase : forall K kb kk om,
  kdescr K = Some (kb, kk, om) -> kbase K = Some kb \/ (exists lo hi, K = KImg lo hi /\ kb = ELit 0%Z /\ kk = lo).
Proof.
  intros K kb kk om H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr kbase] in *; try discriminate; try (injection H as <- <- Hm); try (left; reflexivity).
  right. exists lo, hi. repeat split; congruence.
Qed.
Lemma kdescr_None_kbase : forall K, kdescr K = None -> kbase K = None.
Proof.
  intros K H. destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr kbase] in *; try discriminate; reflexivity.
Qed.

Lemma prune1pcK_keep_based : forall bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc kb = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + kk \/ hi2 + kk + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp wa w wv K false (base_rangeB bc kb) = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hsp Hbr Hnum.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen]; rewrite Hsp, Hbr;
    refold_leb; match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end.
Qed.

Lemma prune1pcK_keep_img : forall bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc (ELit 0%Z) = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + lo \/ hi2 + lo + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2 HD Hne Hsp Hbr Hnum.
  cbn [kdescr] in HD. change (2 ^ 64)%Z with two64 in HD. destruct (Z.ltb (hi - lo) two64) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pB. cbn [elen]. rewrite Hsp, Hbr.
    refold_leb; match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.

Lemma prune1pcK_keep_based_sides : forall bc sp wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  in_sidesB bc (sp_D sp) kb kk m = true ->
  prune1pcK bc sp wa w wv K false br2 = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 HB HD HS.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; cbn [a_base a_off]; unfold elen;
    rewrite (ranges_apart_pcB_sides bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 _ _ _ HS); reflexivity.
Qed.

Lemma prune1pcK_keep_img_sides : forall bc sp wa w wv lo hi m same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  in_sidesB bc (sp_D sp) (ELit 0%Z) lo m = true ->
  prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp wa w wv lo hi m same br2 HD Hne HS.
  cbn [kdescr] in HD. change (2 ^ 64)%Z with two64 in HD. destruct (Z.ltb (hi - lo) two64) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold elen. rewrite (ranges_apart_pB_sides bc sp wb k (Z.of_nat w) _ _ _ HS). reflexivity. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.

(* [comment removed for export] *)
Definition EINF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
  match oi with
  | None => kdescr K = None
  | Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei)
               /\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
               /\ ei_br ei = base_rangeB bc (ei_kb ei)
  end.
Lemma EINF_mono : forall bc t t' K oi,
  (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> EINF bc t K oi -> EINF bc t' K oi.
Proof. intros bc t t' K [ei|] Hm H; cbn [EINF] in *; [|exact H]. destruct H as (A & B & C). split; [exact A|]. split; [apply Hm; exact B| exact C]. Qed.

Lemma scan_entries_ok : forall fk kn t gs infos t' gs',
  NTI (mkbc fk) t -> scan_entries (mkbc fk) kn t gs = (infos, t', gs') ->
  NTI (mkbc fk) t'
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k))
  /\ Forall2 (EINF (mkbc fk) t') kn infos.
Proof.
  intros fk kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
  - cbn [scan_entries] in H.
    destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
    + destruct (intern (mkbc fk) t kb) as [[bid bi] t1] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
      lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
      destruct (scan_entries (mkbc fk) rest t1 _) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
      constructor; [|exact HF]. cbn [EINF ei_kb ei_k ei_m ei_bid ei_br].
      split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity.
    + destruct (scan_entries (mkbc fk) rest t gs) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.

Lemma chainKF_eq : forall bc g sxs K okb same_of br2,
  (forall sx rest, In sx sxs -> verdict sx g = true ->
     chainK2 bc (sx :: rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2) ->
  chainKF bc (mk_fl g sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
  cbn [mk_fl].
  assert (IH' : chainKF bc (mk_fl g rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros sx0 rest0 Hin Hv0; apply Hf; [right|]; assumption).
  destruct (verdict sx g) eqn:Hv.
  - rewrite (Hf sx rest (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF chainK2]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma zlit64_small : forall z, (0 <= z < two64)%Z -> zlit64 z = z.
Proof. intros z H. unfold zlit64. change (if Z.leb 0 z then Z.ltb z two64 else false) with (Z.leb 0 z && Z.ltb z two64)%bool in *; replace (Z.leb 0 z && Z.ltb z two64)%bool with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma prune1pcK_same_apart : forall bc sp wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) -> knormal K = true ->
  (a_off wa + Z.of_nat w <= kk \/ kk + m <= a_off wa)%Z ->
  prune1pcK bc sp wa w wv K true br2 = PKeep \/ prune1pcK bc sp wa w wv K true br2 = PRepl [K].
Proof.
  intros bc sp [wb k] w wv K kb kk m br2 HB HD HN Hap. cbn [a_off] in Hap.
  assert (TRIM : forall (mk : saddr -> expr -> kentry) z, (0 < z < two64)%Z -> (k + Z.of_nat w <= kk \/ kk + z <= k)%Z ->
            ktrim mk kb kk z k w = [mk (SA kb kk) (ELit z)]).
  { intros mk z Hz Hd. unfold ktrim. change (2 ^ 64)%Z with two64. rewrite (Z.mod_small z two64) by lia.
    destruct Hd as [Hd|Hd].
    - replace (Z.ltb kk (Z.min k (kk + z))) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (Z.max kk (k + Z.of_nat w)) with kk by lia.
      replace (Z.ltb kk (kk + z)) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [app]. repeat f_equal. lia.
    - replace (Z.min k (kk + z)) with (kk + z)%Z by lia.
      replace (Z.ltb kk (kk + z)) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z.ltb (Z.max kk (k + Z.of_nat w)) (kk + z)) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn [app]. repeat f_equal. lia. }
  destruct K as [[b k0] w' v|[b k0] len|[b k0] len bk|lo hi|e' m'|e' lo' hi'|[b k0] n|a1 n1 a2 n2|[b k0] len fc|[b k0] len];
    cbn [kbase kdescr knormal] in HB, HD, HN; try discriminate.
  - (* [comment removed for export] *) injection HB as ->. injection HD as <- <-. apply Z.ltb_lt in HN.
    rewrite zlit64_small in Hap by lia. left. unfold prune1pcK. cbn [a_base a_off].
    change (if Z.leb (k0 + Z.of_nat w') k then true else Z.leb (k + Z.of_nat w) k0) with (Z.leb (k0 + Z.of_nat w') k || Z.leb (k + Z.of_nat w) k0)%bool in *; replace (Z.leb (k0 + Z.of_nat w') k || Z.leb (k + Z.of_nat w) k0)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. destruct Hap as [H|H]; [right|left]; apply Z.leb_le; lia.
  - (* [comment removed for export] *) destruct len as [z| | | | | | |]; try discriminate. injection HB as ->. injection HD as <- <-.
    apply andb_prop in HN as [H0 H1]. apply Z.ltb_lt in H0. apply Z.ltb_lt in H1. rewrite zlit64_small in Hap by lia.
    right. unfold prune1pcK. cbn [a_base a_off]. rewrite (TRIM KZero z) by lia. reflexivity.
  - (* [comment removed for export] *) destruct len as [z| | | | | | |]; try discriminate. injection HB as ->. injection HD as <- <-.
    apply andb_prop in HN as [H0 H1]. apply Z.ltb_lt in H0. apply Z.ltb_lt in H1. rewrite zlit64_small in Hap by lia.
    left. unfold prune1pcK. cbn [a_base a_off]. change (2 ^ 64)%Z with two64. rewrite (Z.mod_small z two64) by lia.
    change (if Z.leb (k0 + z) k then true else Z.leb (k + Z.of_nat w) k0) with (Z.leb (k0 + z) k || Z.leb (k + Z.of_nat w) k0)%bool in *; replace (Z.leb (k0 + z) k || Z.leb (k + Z.of_nat w) k0)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. destruct Hap as [H|H]; [right|left]; apply Z.leb_le; lia.
  - (* [comment removed for export] *) destruct len as [z| | | | | | |]; try discriminate. injection HB as ->. injection HD as <- <-.
    apply andb_prop in HN as [H0 H1]. apply Z.ltb_lt in H0. apply Z.ltb_lt in H1. rewrite zlit64_small in Hap by lia.
    right. unfold prune1pcK. cbn [a_base a_off]. rewrite (TRIM (fun a n => KFill a n fc) z) by lia. reflexivity.
  - (* [comment removed for export] *) destruct len as [z| | | | | | |]; try discriminate. injection HB as ->. injection HD as <- <-.
    apply andb_prop in HN as [H0 H1]. apply Z.ltb_lt in H0. apply Z.ltb_lt in H1. rewrite zlit64_small in Hap by lia.
    right. unfold prune1pcK. cbn [a_base a_off]. rewrite (TRIM KUnk z) by lia. reflexivity.
Qed.

Lemma kdescr_m_bounds : forall K kb kk m, kdescr K = Some (kb, kk, Some m) -> (0 <= m < two64)%Z.
Proof.
  intros K kb kk m H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr] in H; try discriminate;
    try (injection H as _ _ <-; apply zlit64_bounds);
    try (destruct len as [z| | | | | | |]; try discriminate; injection H as _ _ <-; apply zlit64_bounds).
  destruct (Z.ltb (hi - lo) (2 ^ 64)); [|discriminate]. injection H as _ _ <-. apply zlit64_bounds.
Qed.

Lemma obr_eqb_eq : forall a b, obr_eqb a b = true -> a = b.
Proof.
  intros [[x1 y1]|] [[x2 y2]|] H; cbn [obr_eqb] in H; try discriminate; [|reflexivity].
  apply andb_prop in H as [X Y]. apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma verdict_inb : forall sx g ei m,
  verdict sx g = true -> inb g ei = true -> ei_m ei = Some m ->
  (Pos.eqb (ei_bid ei) (sx_bid sx) = true
   /\ (a_off (sx_a sx) + Z.of_nat (sx_w sx) <= ei_k ei \/ ei_k ei + m <= a_off (sx_a sx))%Z)
  \/ (Pos.eqb (ei_bid ei) (sx_bid sx) = false
      /\ ((exists lo1 hi1 lo2 hi2, sp_rng (sx_sp sx) = Some (lo1, hi1) /\ ei_br ei = Some (lo2, hi2)
            /\ (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx)) <= lo2 + ei_k ei \/ hi2 + ei_k ei + m <= lo1 + a_off (sx_a sx))%Z)
          \/ (exists glo ghi, existsb (hull_in_side (ei_kb ei) (ei_br ei) glo ghi) (sp_D (sx_sp sx)) = true
                              /\ (glo <= ei_k ei)%Z /\ (ei_k ei + m <= ghi)%Z))).
Proof.
  intros sx [[[b kb] obr] [glo ghi]] ei m Hv Hi Hm. unfold verdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1k].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
  apply p_expr_eqb_eq in H1k. subst kb. apply obr_eqb_eq in H2. subst obr.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)).
  { left. split; [reflexivity|]. apply Bool.orb_prop in Hv. destruct Hv as [H|H]; apply Z.leb_le in H; lia. }
  right. split; [reflexivity|].
  match type of Hv with (if ?c then true else _) = true => destruct c eqn:Hnum end.
  - left. destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate].
    destruct (ei_br ei) as [[lo2 hi2]|]; [|discriminate].
    exists lo1, hi1, lo2, hi2. split; [reflexivity|]. split; [reflexivity|].
    unfold sx_m1 in Hnum. apply Bool.orb_prop in Hnum. destruct Hnum as [H|H]; apply Z.leb_le in H; lia.
  - right. exists glo, ghi. split; [exact Hv|]. split; assumption.
Qed.

Lemma entriesG_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sxs (mk_gl bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINF] in HK.
    + destruct HK as (HD & HIn & Hbr).
      (* [comment removed for export] *)
      assert (FULL : forall okb, okb = kbase K ->
        chainK2 (mkbc fk) sxs K okb
          (match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
          (match okb with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
      { intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb|].
        destruct okb as [kb|]; [|reflexivity].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hokb; discriminate].
        rewrite <- Hokb in HB. injection HB as ->.
        split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
      unfold mk_gl. rewrite pt_get_map.
      destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      destruct (knormal K) eqn:HN; [|apply FULL; reflexivity].
      rewrite <- (FULL (kbase K) eq_refl). apply chainKF_eq.
      intros sx rest' Hsx Hv.
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
      rewrite Hm in HD.
      destruct (verdict_inb _ _ _ _ Hv Hinb Hm) as [(Heq & Hap)|(Hne & [(lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum)|(glo & ghi & HEX & Hglo & Hghi)])].
      { (* [comment removed for export] *)
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|discriminate HN].
        rewrite HB. cbn [chainK2]. rewrite Heq.
        destruct (prune1pcK_same_apart (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K _ _ _ (ei_br ei) HB HD HN Hap) as [Hp|Hp]; rewrite Hp; [reflexivity|].
        cbn [flat_map]. rewrite HB, p_expr_eqb_refl, app_nil_r. reflexivity. }
      { destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        * rewrite HB. cbn [chainK2]. rewrite Hne. rewrite Hbr.
          rewrite (prune1pcK_keep_based (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K _ _ _ lo1 hi1 lo2 hi2 HB HD Hsp ltac:(rewrite <- Hbr; exact Hbr2) Hnum). reflexivity.
        * discriminate HN. }
      (* [comment removed for export] *)
      assert (HSD : in_sidesB (mkbc fk) (sp_D (sx_sp sx)) (ei_kb ei) (ei_k ei) m = true).
      { eapply in_sidesB_of_hull; [exact HEX | symmetry; exact Hbr | exact Hglo | exact Hghi | eapply kdescr_m_bounds; exact HD]. }
      destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
      * rewrite HB. cbn [chainK2]. rewrite Hne.
        rewrite (prune1pcK_keep_based_sides (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K _ _ _ _ HB HD HSD). reflexivity.
      * discriminate HN.
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.

Lemma carryG_eq : forall log kn,
  carryG (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryG.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.

Definition carryK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK_eq : forall log kn hints,
  carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical, carryG_eq. reflexivity.
Qed.

End AX2B.
