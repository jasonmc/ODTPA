#!/usr/bin/env python
# encoding: utf-8
"""
odtpa.py

Created by Jason McCandless on 2007-10-26.
"""

import sys
import os

infinity = 1e300000 #float infinity. could use sys.max_int
debug = True

class Non_term:
	def __init__(self,name):
		self.name = name
	def __str__(self):
		return str(self.name)
	def __hash__(self):
		return hash(self.name)
	def __eq__(self,other):
		return self.name == other.name
		
class Term:
	def __init__(self,name):
		self.name = name
	def __str__(self):
		return str(self.name)
	def __hash__(self):
		return hash(self.name)
	def __eq__(self,other):
		return self.name == other.name
		
class Pattern:
	def __init__(self,op,child1=None,child2=None):
		self.op = op
		self.child1 = child1
		self.child2 = child2
		
	def __str__(self):
		string = str(self.op)
		if self.child1:
			string += "(" + str(self.child1)
			if self.child2:
				string += ", " + str(self.child2)
			string += ")"
		
		return string

class Grammar_rule:
	def __init__(self,num,nt,pattern,cost):
		self.num = num
		self.nt = nt
		self.pattern = pattern
		self.cost = cost
		
		self.dyncost = False if isinstance(cost,int) else True
		
	def __str__(self):
		return str(self.num) + "  " + str(self.nt) + " -> " + str(self.pattern) + " " + str(self.cost)

class Tree_node:
	def __init__(self,nt,child1=None,child2=None):
		self.nt = nt #probably should not be nt, in fact we only have terms in the tree
		self.child1 = child1
		self.child2 = child2
		
	def __str__(self):
		string = str(self.nt)
		if self.child1:
			string += "(" + str(self.child1)
			if self.child2:
				string += ", " + str(self.child2)
			string += ")"
		
		return string
		
	# def __hash__(self):
	# 	if self.child1:
	# 		if self.child2:
	# 			return hash((self.nt,self.child1,self.child2))
	# 		else:
	# 			return hash((self.nt,self.child1,None))
	# 	else:
	# 		return hash((self.nt,None,None))		

	def __hash__(self):
		if self.child1:
			if self.child2:
				return hash((self.nt,self.child1.state.num,self.child2.state.num))
			else:
				return hash((self.nt,self.child1.state.num,None))
		else:
			return hash((self.nt,None,None))
	
	def __eq__(self,other):
		if self.child1:
			if not other.child1:
				return False
			if self.child2:
				if not other.child2:
					return False
				return self.nt == other.nt and self.child1.state.num == other.child1.state.num and self.child2.state.num == other.child2.state.num
			else:
				return self.nt == other.nt and self.child1.state.num == other.child1.state.num
		else:
			return self.nt == other.nt

class State_nt:
	def __init__(self,nt):
		self.nt = nt
		self.cost = infinity
		self.rule = None
	def __str__(self):
		return str(self.nt) + " " + str(self.cost) + " rule: " + str(self.rule)
		
	def __hash__(self):
		return hash(self.nt)

state_num=0
		
class State:
	def __init__(self,grammar):
		global state_num
		state_num += 1
		self.num = state_num
		
		self.nts = {}
		for g in grammar:
			if not g.nt in self.nts:
				self.nts[g.nt] = State_nt(g.nt)
			
	def __getitem__(self, k):		
		return self.nts[k]
		
	def __str__(self):
		s = str(self.num) + "\n"
		for _,y in self.nts.items():
			s += str(y) + "\n"
		return s
		
	def __hash__(self):
		return hash((tuple([x.rule for _,x in self.nts.items()]),tuple([x.cost for _,x in self.nts.items()])))
		
	def __eq__(self,other):
		srules = [x.rule for _,x in self.nts.items()]
		orules = [x.rule for _,x in other.nts.items()]
		
		if srules != orules:
			return False
		
		scosts = [x.cost for _,x in self.nts.items()]
		ocosts = [x.cost for _,x in other.nts.items()]
		
		if scosts != ocosts:
			return False
			
		return True
		
		
def newstate(n,grammar):
	s = State(grammar)
		
	#for r in rules matching "x -> op(x[1], .., x[m])" where op=n.op
	for r in grammar:
		if r.pattern.op == n.nt: #non-term is interchangable with op # and 'r.pattern.child1'
			#cost = r.cost + sum(n.child[i].state[x[i]].cost where i in 1..m)
			cost = r.cost
			
			if n.child1:
				if isinstance(r.pattern.child1,Term):
					if r.pattern.child1.name != n.child1.nt.name:
						cost = infinity
				else:
					cost += n.child1.state[r.pattern.child1].cost
			
			if n.child2:
				if isinstance(r.pattern.child2,Term):
					if r.pattern.child2.name != n.child2.nt.name:
						cost = infinity
				else:
					cost += n.child2.state[r.pattern.child2].cost
		
			if cost < s[r.nt].cost:
				s[r.nt].cost = cost
				s[r.nt].rule = r
			
		
	s_change = True
	while (s_change):
		s_change = False
		#for r in rules matching "x -> y" where y is a nonterminal
		for r in grammar:
			if not r.pattern.child1 and isinstance(r.pattern.op,Non_term):
			
				cost = r.cost + s[r.pattern.op].cost
				if cost < s[r.nt].cost:
					s[r.nt].cost = cost
					s[r.nt].rule = r
					s_change = True
					
	return s

def label_dynamic(tree,grammar):
	# for n in nodes(tree), in bottom up order
	# 	n.state = newstate(n,grammar)
	if tree.child1:
		label_dynamic(tree.child1,grammar)
		if tree.child2:
			label_dynamic(tree.child2,grammar)
			
	tree.state = newstate(tree,grammar)
	
	if debug:
		print "==STATE==  " + str(tree)
		print str(tree.state)


def reduce(root,start): #Tree
	r = root.state[start].rule
	
	if not r.pattern.child1 and isinstance(r.pattern.op,Non_term):
		reduce(root,r.pattern.op)
	else:
		if r.pattern.child1 and isinstance(r.pattern.child1,Non_term):
			reduce(root.child1,r.pattern.child1)
		if r.pattern.child2 and isinstance(r.pattern.child2,Non_term):
			reduce(root.child2,r.pattern.child2)
				
	print r.num

states = {}

def label_simple(tree,grammar):
	if tree.child1:
		label_simple(tree.child1,grammar)
		if tree.child2:
			label_simple(tree.child2,grammar)
			
	#n matches op(n1, ..., nm)
	if isinstance(tree.nt,Term):
		if tree in states:
			s = states[tree]
		else:
			s = newstate(tree,grammar)
			states[tree] = s
		tree.state = s
		
		if debug:
			print "==STATE==  " + str(tree)
			print str(s)


def normalize(s):
	delta = min([s[x].cost for x in s.nts])
	
	for x in s.nts:
		s[x].cost = s[x].cost - delta
		
	return s

allstates = {}

def label_equiv(tree,grammar):
	
	if tree.child1:
		label_equiv(tree.child1,grammar)
		if tree.child2:
			label_equiv(tree.child2,grammar)

	#n matches op(n1, ..., nm)
	if isinstance(tree.nt,Term):
		# key = hash(tree)
		
		if tree in states:
			s = states[tree]
		else:
			s = newstate(tree,grammar)
			s = normalize(s)
			if s in allstates:
				s = allstates[s]
			else:
				allstates[s] = s
			states[tree] = s
			
		tree.state = s
		
		if debug:
			print "==STATE==  " + str(tree)
			print str(s)

# def newswdc(n,):
# 	s = State(grammar)
# 	
# 	s.dynrules = None
# 	
# 	for r in grammar:
# 		if r.dyncost:
# 			s.dynrules += [r]
# 			
# 	return s
# 	
# swdcs = {}
# 			
# def label_dyncost(tree):
# 	if tree.child1:
# 		label_dyncost(tree.child1,grammar)
# 		if tree.child2:
# 			label_dyncost(tree.child2,grammar)
# 			
# 	#n matches op(n1, ..., nm)		
# 	if tree in swdcs:
# 		s = swdcs[tree]
# 	else:
# 		s = newswdc(n)
# 		swdcs[tree] = s
# 	key1 = None
# 	for r in s.dynrules:
# 		key1 += [r.cost]
# 		#evaluate!
# 	if (s.id,key1) in index(states):
# 		s1 = states[(s.id, key1)]
# 	else:
# 		s1 = newstate(n)
# 		#evaluate!
# 		states[(s,key1)] = s1
# 		
# 	n.state = s1
		

def main():
	
	grammar = []
	grammar += [Grammar_rule(1,Non_term('start'), Pattern(Non_term('reg')),0)]
	grammar += [Grammar_rule(2,Non_term('reg'), Pattern(Term('Reg')),0)]
	grammar += [Grammar_rule(3,Non_term('reg'), Pattern(Term('Int')),1)]
	grammar += [Grammar_rule(4,Non_term('reg'), Pattern(Term('Fetch'),Non_term('addr')),2)]
	grammar += [Grammar_rule(5,Non_term('reg'), Pattern(Term('Plus'),Non_term('reg'),Non_term('reg')),2)]
	grammar += [Grammar_rule(6,Non_term('addr'), Pattern(Non_term('reg')),0)]
	grammar += [Grammar_rule(7,Non_term('addr'), Pattern(Term('Int')),0)]
	grammar += [Grammar_rule(8,Non_term('addr'), Pattern(Term('Plus'),Non_term('reg'),Term('Int')),0)]
	
	norm_grammar = []
	norm_grammar += [Grammar_rule(1,Non_term('start'), Pattern(Non_term('reg')),0)]
	norm_grammar += [Grammar_rule(2,Non_term('reg'), Pattern(Term('Reg')),0)]
	norm_grammar += [Grammar_rule(3,Non_term('reg'), Pattern(Term('Int')),1)]
	norm_grammar += [Grammar_rule(4,Non_term('reg'), Pattern(Term('Fetch'),Non_term('addr')),2)]
	norm_grammar += [Grammar_rule(5,Non_term('reg'), Pattern(Term('Plus'),Non_term('reg'),Non_term('reg')),2)]
	norm_grammar += [Grammar_rule(6,Non_term('addr'), Pattern(Non_term('reg')),0)]
	norm_grammar += [Grammar_rule(7,Non_term('addr'), Pattern(Term('Int')),0)]
	norm_grammar += [Grammar_rule(8,Non_term('addr'), Pattern(Term('Plus'),Non_term('reg'),Non_term('n1')),0)]
	norm_grammar += [Grammar_rule(9,Non_term('n1'),Pattern(Term('Int')),0)]
		
	tn = Tree_node
	tree = tn(Term('Fetch'),tn(Term('Fetch'),tn(Term('Plus'),tn(Term('Reg')),tn(Term('Int')))))
	
	# for x in grammar:
	# 	print x
	# 	
	# print tree
	
	#label_simple(tree,grammar)
	
	label_equiv(tree,norm_grammar)

	reduce(tree,Non_term('start'))
	
if __name__ == '__main__':
	main()

