(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition B64_EOLN : Z := 240.  Definition B64_CR : Z := 241.  Definition B64_EOF : Z := 242.
Definition B64_WS : Z := 224.    Definition B64_ERROR : Z := 255.
Definition data_ascii2bin : list Z :=
  [255;255;255;255;255;255;255;255;255;224; 240;255;255;241;255;255;255;255;255;255;
   255;255;255;255;255;255;255;255;255;255; 255;255;224;255;255;255;255;255;255;255;
   255;255;255;62;255;242;255;63;52;53;     54;55;56;57;58;59;60;61;255;255;
   255;0;255;255;255;0;1;2;3;4;             5;6;7;8;9;10;11;12;13;14;
   15;16;17;18;19;20;21;22;23;24;           25;255;255;255;255;255;255;26;27;28;
   29;30;31;32;33;34;35;36;37;38;           39;40;41;42;43;44;45;46;47;48;
   49;50;51;255;255;255;255;255].
(* [comment removed for export] *)
Definition a2b (c : Z) : Z := if 128 <=? c then B64_ERROR else nth (Z.to_nat c) data_ascii2bin B64_ERROR.
Definition b64_not_base64 (v : Z) : bool := Z.lor v 19 =? 243.
Definition b64_base64 (v : Z) : bool := negb (b64_not_base64 v).
Definition CH_EQ : Z := 61.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint trim_ws_front (f : list Z) : list Z :=
  match f with c :: f' => if a2b c =? B64_WS then trim_ws_front f' else f | [] => [] end.
Fixpoint trim_nb64_back_rev (r : list Z) (keep : nat) : list Z :=   (* [comment removed for export] *)
  match r with
  | c :: r' => if (Nat.ltb 3 (length r)) && b64_not_base64 (a2b c) then trim_nb64_back_rev r' keep else r
  | [] => []
  end.
Definition trim_block (f : list Z) : list Z :=
  let f1 := trim_ws_front f in rev (trim_nb64_back_rev (rev f1) 0%nat).
Definition quad_val (a b c d : Z) : Z := a * 262144 + b * 4096 + c * 64 + d.
Definition quad_bytes (l : Z) : list Z := [l / 65536 mod 256; l / 256 mod 256; l mod 256].
(* [comment removed for export] *)
Fixpoint decode_groups (vs : list Z) : option (list Z) :=
  match vs with
  | a :: b :: c :: d :: rest =>
      if 128 <=? Z.lor (Z.lor (Z.lor a b) c) d then None   (* [comment removed for export] *)
      else match decode_groups rest with None => None | Some bs => Some (quad_bytes (quad_val a b c d) ++ bs) end
  | _ => Some []
  end.
Definition decodeblock (f : list Z) (eof : Z) : option (list Z) :=
  if (eof <? -1) || (2 <? eof) then None else
  let f' := trim_block f in
  let n := Z.of_nat (length f') in
  if negb (n mod 4 =? 0) then None
  else if n =? 0 then Some []
  else
    let vs := map a2b f' in
    match decode_groups vs with
    | None => None
    | Some bs =>
        let c := nth (Z.to_nat (n - 2)) vs 0 in let d := nth (Z.to_nat (n - 1)) vs 0 in
        let eof' := if eof =? -1 then (if c =? CH_EQ then 1 else 0) + (if d =? CH_EQ then 1 else 0) else eof in
        Some (firstn (length bs - Z.to_nat eof') bs)
    end.
Definition decodeblock_ret (f : list Z) (eof : Z) : Z :=
  match decodeblock f eof with None => -1 | Some bs => Z.of_nat (length bs) end.

(* [comment removed for export] *)
Record dustate := mkDU { du_d : list Z; du_eof : Z; du_out : list Z }.
Definition initial_eof (d : list Z) : Z :=
  let n := length d in
  if (Nat.ltb 0 n) && (nth (n - 1) d 0 =? CH_EQ)
  then (if (Nat.ltb 1 n) && (nth (n - 2) d 0 =? CH_EQ) then 2 else 1) else 0.
(* [comment removed for export] *)
Inductive dustep_r := DUerr (d' : list Z) | DUcont (st' : dustate) | DUeof (st' : dustate).
Definition du_step (st : dustate) (tmp : Z) : dustep_r :=
  let v := a2b tmp in
  if v =? B64_ERROR then DUerr (du_d st) else
  let eof1 := if tmp =? CH_EQ then du_eof st + 1 else du_eof st in
  if negb (tmp =? CH_EQ) && (0 <? du_eof st) && b64_base64 v then DUerr (du_d st) else
  if 2 <? eof1 then DUerr (du_d st) else
  if v =? B64_EOF then DUeof (mkDU (du_d st) eof1 (du_out st)) else
  if b64_base64 v && Nat.leb 64 (length (du_d st)) then DUerr (du_d st) else
  let d1 := if b64_base64 v then du_d st ++ [tmp] else du_d st in
  if Nat.eqb (length d1) 64 then
    match decodeblock d1 eof1 with
    | None => DUerr []
    | Some bs => if Nat.eqb (length bs) 0 && (0 <? eof1) then DUerr []
                 else DUcont (mkDU [] eof1 (du_out st ++ bs))
    end
  else DUcont (mkDU d1 eof1 (du_out st)).
(* [comment removed for export] *)
Record duresult := mkDR { dr_rv : Z; dr_out : list Z; dr_d : list Z }.
(* [comment removed for export] *)
Definition du_tail (st : dustate) (seof : bool) : duresult :=
  let n := length (du_d st) in
  if Nat.ltb 0 n then
    if Nat.eqb (Nat.modulo n 4) 0 then
      match decodeblock (du_d st) (du_eof st) with
      | None => mkDR (-1) (du_out st) []
      | Some bs => if Nat.eqb (length bs) 0 && (0 <? du_eof st) then mkDR (-1) (du_out st) []
                   else mkDR (if seof || (0 <? du_eof st) then 0 else 1) (du_out st ++ bs) []
      end
    else if seof then mkDR (-1) (du_out st) (du_d st)
    else mkDR 1 (du_out st) (du_d st)
  else mkDR (if seof || (0 <? du_eof st) then 0 else 1) (du_out st) [].
Fixpoint du_loop (st : dustate) (inp : list Z) : duresult :=
  match inp with
  | [] => du_tail st false
  | c :: inp' =>
      match du_step st c with
      | DUerr d' => mkDR (-1) (du_out st) d'
      | DUeof st' => du_tail st' true
      | DUcont st' => du_loop st' inp'
      end
  end.
(* [comment removed for export] *)
Definition decode_update (d : list Z) (inp : list Z) : duresult :=
  match inp with
  | [] => mkDR 0 [] d
  | _ => du_loop (mkDU d (initial_eof d) []) inp
  end.
(* [comment removed for export] *)
Definition decode_final_rv (d : list Z) : Z :=
  if Nat.eqb (length d) 0 then 1 else if decodeblock_ret d (-1) <? 0 then -1 else 1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record b64r_res := mkBR { br_rv : Z; br_out : list Z; br_used : nat }.
Fixpoint b64r_loop (fuel : nat) (rest : list Z) (d : list Z) (ret outl : Z) (acc : list Z) (used : nat) : b64r_res :=
  match fuel with
  | O => mkBR (if ret =? 0 then 0 else ret) acc used
  | S fuel' =>
      if outl <=? 0 then mkBR ret acc used
      else match rest with
      | [] => mkBR (if ret =? 0 then (if decode_final_rv d <? 0 then -1 else 0) else ret) acc used
      | _ =>
          let chunk := firstn 1024 rest in
          let r := decode_update d chunk in
          let used' := (used + length chunk)%nat in
          if dr_rv r <? 0 then mkBR (if ret =? 0 then 0 else ret) acc used'
          else
            let i := Z.min (Z.of_nat (length (dr_out r))) outl in
            let acc' := acc ++ firstn (Z.to_nat i) (dr_out r) in
            if dr_rv r =? 0 then mkBR (if ret + i =? 0 then 0 else ret + i) acc' used'
            else b64r_loop fuel' (skipn 1024 rest) (dr_d r) (ret + i) (outl - i) acc' used'
      end
  end.
Definition b64_read_spec (txt : list Z) (outl : Z) : b64r_res := b64r_loop (S (S (length txt))) txt [] 0 outl [] 0%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Example t_foobar : dr_out (decode_update [] [90;109;57;118;89;109;70;121]) = [102;111;111;98;97;114]
                 /\ dr_rv (decode_update [] [90;109;57;118;89;109;70;121]) = 1
                 /\ dr_d (decode_update [] [90;109;57;118;89;109;70;121]) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Example t_foob : dr_out (decode_update [] [90;109;57;118;89;103;61;61]) = [102;111;111;98]
               /\ dr_rv (decode_update [] [90;109;57;118;89;103;61;61]) = 0.
Proof. vm_compute. split; reflexivity. Qed.
(* [comment removed for export] *)
Example t_part : dr_out (decode_update [] [90;109;57;118;89]) = [] /\ dr_d (decode_update [] [90;109;57;118;89]) = [90;109;57;118;89]
               /\ dr_rv (decode_update [] [90;109;57;118;89]) = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Example t_bad : dr_rv (decode_update [] [90;109;57;59]) = -1.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example t_final : decode_final_rv [90;109;57;118;89] = -1 /\ decode_final_rv [] = 1.
Proof. vm_compute. split; reflexivity. Qed.
(* [comment removed for export] *)
Example t_68 : dr_out (decode_update [] [81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68]) = [65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67;65;66;67]
             /\ dr_rv (decode_update [] [81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68]) = 1 /\ dr_d (decode_update [] [81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68;81;85;74;68]) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Example t_carry : dr_out (decode_update [81;85;74] [68;81;85;74;68]) = [65;66;67;65;66;67]
             /\ dr_d (decode_update [81;85;74] [68;81;85;74;68]) = [].
Proof. vm_compute. split; reflexivity. Qed.
(* [comment removed for export] *)
Example t_read : br_rv (b64_read_spec [90;109;57;118;89;109;70;121] 8) = 6
               /\ br_out (b64_read_spec [90;109;57;118;89;109;70;121] 8) = [102;111;111;98;97;114]
               /\ br_used (b64_read_spec [90;109;57;118;89;109;70;121] 8) = 8%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Example t_read5 : br_rv (b64_read_spec [90;109;57;118;89] 5) = -1 /\ br_out (b64_read_spec [90;109;57;118;89] 5) = [].
Proof. vm_compute. split; reflexivity. Qed.
