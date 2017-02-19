(** Definition of the physical memory model **)
Require Export lib.Coqlib.
Require Export Integers.
Open Local Scope Z_scope.
Require Import iris.base_logic.base_logic.

Definition block : Set := positive.
Definition offset := Z.
Definition addr : Set := prod block offset.

Instance addr_eq_dec : EqDecision addr.
Proof. solve_decision. Defined.

Inductive byteval : Set :=
| BVundef
| BVint8 (i: int8)
| BVaddr (p: addr) (k: nat)
| BVnull.

(* (**Encoding and decoding for values**) *)
(* Fixpoint encode_int (n: nat) (x: Z) {struct n}: list byte := *)
(*   match n with *)
(*     | O => nil *)
(*     | S m => Byte.repr x :: encode_int m (x / 256) *)
(*   end. *)

(* Fixpoint decode_int (l: list byte): Z := *)
(*   match l with *)
(*     | nil => 0 *)
(*     | b :: l' => Byte.unsigned b + decode_int l' * 256 *)
(*   end. *)

(* Lemma encode_int_length: *)
(*   forall sz x, length(encode_int sz x) = sz. *)
(* Proof. *)
(*   induction sz; simpl; intros. auto. decEq. auto. *)
(* Qed. *)

(* Definition inj_bytes (bl: list byte) : list memval := *)
(*   List.map Byte bl. *)

(* Fixpoint proj_bytes (vl: list memval) : option (list byte) := *)
(*   match vl with *)
(*     | nil => Some nil *)
(*     | Byte b :: vl' => *)
(*       match proj_bytes vl' with None => None | Some bl => Some(b :: bl) end *)
(*     | _ => None *)
(*   end. *)

(* Lemma length_inj_bytes: *)
(*   forall bl, length (inj_bytes bl) = length bl. *)
(* Proof. *)
(*   intros. apply List.map_length. *)
(* Qed. *)

(* Lemma proj_inj_bytes: *)
(*   forall bl, proj_bytes (inj_bytes bl) = Some bl. *)
(* Proof. *)
(*   induction bl; simpl. auto. rewrite IHbl. auto. *)
(* Qed. *)

(* Lemma inj_proj_bytes: *)
(*   forall cl bl, proj_bytes cl = Some bl -> cl = inj_bytes bl. *)
(* Proof. *)
(*   induction cl; simpl; intros. *)
(*   inv H; auto. *)
(*   destruct a; try congruence. destruct (proj_bytes cl); inv H. *)
(*   simpl. decEq. auto. *)
(* Qed. *)

(* Fixpoint inj_pointer (n: nat) (b: block) (ofs: int32) {struct n}: list memval := *)
(*   match n with *)
(*     | O => nil *)
(*     | S m => Pointer b ofs m :: inj_pointer m b ofs *)
(*   end. *)

(* Fixpoint check_pointer (n: nat) (b: block) (ofs: int32) (vl: list memval) *)
(*          {struct n} : bool := *)
(*   match n, vl with *)
(*     | O, nil => true *)
(*     | S m, Pointer b' ofs' m' :: vl' => *)
(*       peq b b' && Int.eq_dec ofs ofs' && beq_nat m m' && check_pointer m b ofs vl' *)
(*     | _, _ => false *)
(*   end. *)


(* Definition proj_pointer (vl: list memval) : val := *)
(*   match vl with *)
(*     | Pointer b ofs n :: vl' => *)
(*       if check_pointer 4%nat b ofs vl then Vptr (b, ofs) else Vundef *)
(*     | _ => Vundef *)
(*   end. *)

(* Definition encode_val (t: type) (v: val) : list memval := *)
(*   match v, t with *)
(*   | Vint32  n, Tint8  => inj_bytes (encode_int 1%nat (Int.unsigned n)) *)
(*   | Vint32  n, Tint16 => inj_bytes (encode_int 2%nat (Int.unsigned n)) *)
(*   | Vint32  n, Tint32 => inj_bytes (encode_int 4%nat (Int.unsigned n)) *)
(*   | Vptr (b, ofs), Tptr _ => inj_pointer 4%nat b (ofs) *)
(*   | Vptr (b, ofs), Tcom_ptr _ => inj_pointer 4%nat b (ofs) *)
(*   | Vnull, Tnull => list_repeat 4 MNull *)
(*   | Vnull, Tptr _ => list_repeat 4 MNull *)
(*   | Vnull, Tcom_ptr _ => list_repeat 4 MNull *)
(*   | _, _ => list_repeat (typelen t) Undef *)
(*   end. *)

(* Definition decode_val (t: type) (vl: list memval) : val := *)
(*   match proj_bytes vl with *)
(*   | Some bl => *)
(*       match t with *)
(*       | Tint8  => Vint32(Int.zero_ext 8 (Int.repr (decode_int bl))) *)
(*       | Tint16 => Vint32(Int.zero_ext 16 (Int.repr (decode_int bl))) *)
(*       | Tint32 => Vint32(Int.repr(decode_int bl)) *)
(*       | _ => Vundef *)
(*       end *)
(*   | None => *)
(*     match vl with *)
(*       | MNull :: MNull ::MNull :: MNull :: nil=> match t with *)
(*                                  | Tnull => Vnull *)
(*                                  | Tptr _ => Vnull *)
(*                                  | Tcom_ptr _ => Vnull *)
(*                                  | _ => Vundef *)
(*                                end *)
(*       | _ => *)
(*         match t with *)
(*           | Tptr _ => proj_pointer vl *)
(*           | Tcom_ptr _ => proj_pointer vl *)
(*           | _ => Vundef *)
(*         end *)
(*     end *)
(*   end. *)

